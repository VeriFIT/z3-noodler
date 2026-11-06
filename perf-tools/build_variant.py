#!/usr/bin/env python3
"""Builds a variant of z3 from patched sources without a full rebuild.

The patched sources are compiled with the flags of an existing build, and z3 is linked again from the objects of that build, with the
patched objects in place of the original ones.
The build must be up to date (ninja -C build/PRESET z3) and export compile_commands.json (CMAKE_EXPORT_COMPILE_COMMANDS).
--reduce-log links the wrapper of mata::nfa::reduce (instrumentation/reduce_wrap.cpp), which logs every reduction to $REDUCE_LOG,
and applies instrumentation/guard-flag.patch, which marks the reductions allowed by regex::should_reduce.
For sources without today's regex::should_reduce, the guard-flag patch does not apply and is skipped; a patch of such sources can set
the flag reduce_guarded itself.
The variant is build/PRESET/variants/NAME/z3.

Examples:
  build_variant.py counting --reduce-log
  build_variant.py old-bounds --patch old-bounds.patch --reduce-log
"""
import argparse
import json
import shlex
import shutil
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
REPO = TOOLS.parent
WRAPPER = TOOLS / "instrumentation" / "reduce_wrap.cpp"
GUARD_FLAG_PATCH = TOOLS / "instrumentation" / "guard-flag.patch"
# The source whose compile flags (the include paths of mata) the wrapper is compiled with.
WRAPPER_FLAGS_SOURCE = "src/smt/theory_str_noodler/regex.cpp"


def parse_arguments():
    """The command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("name", help="name of the variant (its directory in build/PRESET/variants)")
    parser.add_argument("--preset", default="release", help="the build to reuse: build/PRESET (default: release)")
    parser.add_argument("--patch", action="append", default=[], type=Path, help="apply a patch with repository-relative paths (repeatable)")
    parser.add_argument("--reduce-log", action="store_true", help="link the reduce wrapper and apply guard-flag.patch")
    return parser.parse_args()


def run(command, cwd=None):
    """Runs a command, failing on a non-zero exit code."""
    subprocess.run(command, cwd=cwd, check=True)


def apply_patch(patch, source_dir, sources):
    """Applies a patch to the sources in source_dir and returns whether it applied.

    The sources that the patch touches are copied from the repository first, unless they are already in sources (a set of
    repository-relative paths, which is updated), so that several patches of one source apply one after another.
    git apply runs in source_dir, which is outside the repository, so it takes the paths of the patch as relative to source_dir.
    """
    numstat = subprocess.run(["git", "apply", "--numstat", str(patch)], cwd=source_dir, check=True, capture_output=True, text=True).stdout
    for source in [line.split("\t")[2] for line in numstat.splitlines()]:
        if source not in sources:
            (source_dir / source).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(REPO / source, source_dir / source)
            sources.add(source)
    return subprocess.run(["git", "apply", str(patch)], cwd=source_dir).returncode == 0


def compile_command(entry, source, output, extra_flags=()):
    """The command of a compile_commands.json entry, changed to compile source into output, with extra flags."""
    tokens = shlex.split(entry["command"])
    tokens[tokens.index("-o") + 1] = str(output)
    tokens[tokens.index("-c") + 1] = str(source)
    # quoted includes of the original source resolve from its directory, which the copy is not in
    return tokens + [f"-I{Path(entry['file']).parent}", *extra_flags]


def link_command(build_dir, replaced_objects, output, extra_arguments=()):
    """The link command of z3 in the build, with replaced objects, another output and extra arguments before the libraries."""
    command = subprocess.run(["ninja", "-C", str(build_dir), "-t", "commands", "-s", "z3"], check=True, capture_output=True,
                             text=True).stdout.strip().splitlines()[-1]
    tokens = shlex.split(command)

    # CMake wraps the command as ": && COMMAND && :"
    if tokens[:2] == [":", "&&"] and tokens[-2:] == ["&&", ":"]:
        tokens = tokens[2:-2]
    for old, new in replaced_objects.items():
        tokens[tokens.index(old)] = str(new)

    # the dependency file of the link belongs to the build
    if "-Xlinker" in tokens and tokens[tokens.index("-Xlinker") + 1].startswith("--dependency-file="):
        index = tokens.index("-Xlinker")
        del tokens[index:index + 2]

    index = tokens.index("-o")
    return tokens[:index] + ["-o", str(output), *extra_arguments] + tokens[index + 2:]


def reduce_symbol(link_tokens):
    """The mangled name of mata::nfa::reduce in the mata library of the link."""
    library = next(token for token in link_tokens if token.endswith("libmata.a"))
    symbols = subprocess.run(["nm", "--defined-only", "-g", library], check=True, capture_output=True, text=True).stdout.split()
    names = sorted({symbol for symbol in symbols if symbol.startswith("_ZN4mata3nfa6reduceERKNS0_3NfaE")})
    if len(names) != 1:
        raise SystemExit(f"expected one mata::nfa::reduce in {library}, found {names}")
    return names[0]


def main():
    """Compiles the patched sources (and the wrapper), then links the variant."""
    args = parse_arguments()
    build_dir = REPO / "build" / args.preset
    variant_dir = build_dir / "variants" / args.name
    variant_dir.mkdir(parents=True, exist_ok=True)
    entries = {entry["file"]: entry for entry in json.loads((build_dir / "compile_commands.json").read_text())}

    with tempfile.TemporaryDirectory() as temporary:
        source_dir = Path(temporary)

        # the given patches must apply; the guard flag is skipped for sources without today's regex::should_reduce
        sources = set()
        for patch in args.patch:
            if not apply_patch(patch.resolve(), source_dir, sources):
                raise SystemExit(f"{patch} does not apply")
        if args.reduce_log and not apply_patch(GUARD_FLAG_PATCH, source_dir, sources):
            print(f"{GUARD_FLAG_PATCH.name} does not apply: no reduction is marked as guarded unless a patch sets reduce_guarded")

        # the patched sources, compiled into variant_dir in place of the objects of the build
        compiles, replaced_objects = [], {}
        for source in sorted(sources):
            entry = entries[str(REPO / source)]
            output = variant_dir / (Path(source).stem + ".o")
            compiles.append(compile_command(entry, source_dir / source, output))
            output_in_build = Path(entry["output"])
            replaced_objects[str(output_in_build.relative_to(build_dir) if output_in_build.is_absolute() else output_in_build)] = output

        # the wrapper, linked with --wrap so that the calls of reduce from z3 go through it
        extra_link_arguments = []
        if args.reduce_log:
            symbol = reduce_symbol(link_command(build_dir, {}, "unused"))
            wrapper_object = variant_dir / "reduce_wrap.o"
            flags_entry = entries[str(REPO / WRAPPER_FLAGS_SOURCE)]
            compiles.append(compile_command(flags_entry, WRAPPER, wrapper_object, [f'-DREDUCE_SYMBOL="{symbol}"']))
            extra_link_arguments = [str(wrapper_object), f"-Wl,--wrap={symbol}"]

        # a compilation takes about 1-2 GB of memory
        with ThreadPoolExecutor(max_workers=4) as pool:
            list(pool.map(lambda command: run(command, cwd=build_dir), compiles))

    run(link_command(build_dir, replaced_objects, variant_dir / "z3", extra_link_arguments), cwd=build_dir)
    print(variant_dir / "z3")


if __name__ == "__main__":
    main()
