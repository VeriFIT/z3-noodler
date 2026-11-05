#!/usr/bin/env python3
"""Builds a variant of z3 without a full rebuild: a few sources are compiled from other versions, everything else is reused from a build.

The variant is build/PRESET/variants/NAME/z3.
The build must be up to date (ninja -C build/PRESET z3), and it must export compile_commands.json (CMAKE_EXPORT_COMPILE_COMMANDS).
--replace takes a source from a file or from a git revision, --patch applies a patch (with repository-relative paths) to the sources.
--reduce-log links the wrapper of mata::nfa::reduce (instrumentation/reduce_wrap.cpp), which logs every call to $REDUCE_LOG.

Examples:
  build_variant.py old --replace src/smt/theory_str_noodler/regex.cpp=b2f2ec58f
  build_variant.py stats --reduce-log --patch instrumentation/reduce-tags.patch --patch instrumentation/no-guards.patch
"""
import argparse
import json
import shlex
import shutil
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import benchlib

TOOLS = Path(__file__).resolve().parent
WRAPPER = TOOLS / "instrumentation" / "reduce_wrap.cpp"


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("name", help="name of the variant (its directory in build/PRESET/variants)")
    parser.add_argument("--preset", default="release", help="the build to reuse: build/PRESET")
    parser.add_argument("--replace", action="append", default=[], type=benchlib.parse_name_value, metavar="SOURCE=FILE_OR_REVISION",
                        help="compile the repository source SOURCE from a file or from its version at a git revision")
    parser.add_argument("--patch", action="append", default=[], type=Path, help="apply a patch with repository-relative paths")
    parser.add_argument("--cxxflags", default="", help="extra compiler flags of the replaced sources")
    parser.add_argument("--reduce-log", action="store_true", help="link the reduce wrapper")
    return parser.parse_args()


def run(command, cwd=None):
    subprocess.run(command, cwd=cwd, check=True)


def prepare_sources(replacements, patches, source_dir):
    """Writes the sources to compile into source_dir at their repository-relative paths: the replacements, and the patched files."""
    sources = set()
    for source, origin in replacements:
        target = source_dir / source
        target.parent.mkdir(parents=True, exist_ok=True)
        if Path(origin).is_file():
            shutil.copy(origin, target)
        else:
            target.write_text(subprocess.run(["git", "-C", str(benchlib.REPO), "show", f"{origin}:{source}"], check=True,
                                             capture_output=True, text=True).stdout)
        sources.add(source)
    # git apply runs in source_dir, which is outside the repository, so it treats the paths of the patch as relative to source_dir
    for patch in patches:
        patch = patch.resolve()
        numstat = subprocess.run(["git", "apply", "--numstat", str(patch)], cwd=source_dir, check=True, capture_output=True, text=True).stdout
        for source in [line.split("\t")[2] for line in numstat.splitlines()]:
            if source not in sources:
                (source_dir / source).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(benchlib.REPO / source, source_dir / source)
                sources.add(source)
        run(["git", "apply", str(patch)], cwd=source_dir)
    return sorted(sources)


def compile_command(entry, source, output, extra_flags):
    """The compile command of a compile_commands.json entry, changed to compile source into output, with extra_flags (a list)."""
    tokens = shlex.split(entry["command"])
    replace_argument(tokens, "-o", str(output))
    replace_argument(tokens, "-c", str(source))
    # quoted includes of the original source resolve from its directory, which the copy is not in
    return tokens + [f"-I{Path(entry['file']).parent}"] + extra_flags


def object_in_link(entry, build_dir):
    """The path of the object of a compile_commands.json entry as the link command names it (relative to the build)."""
    output = Path(entry["output"])
    return str(output.relative_to(build_dir) if output.is_absolute() else output)


def replace_argument(tokens, flag, value):
    index = tokens.index(flag)  # fails if the flag is missing
    tokens[index + 1] = value


def link_command(build_dir, replaced_objects, variant_z3, extra):
    """The link command of z3 in the build, with the replaced objects, the output variant_z3 and the extra arguments before the libraries."""
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
    output = tokens.index("-o")
    return tokens[:output] + ["-o", str(variant_z3)] + extra + tokens[output + 2:]


def reduce_symbol(link_tokens):
    """The mangled name of mata::nfa::reduce in the mata library of the link."""
    library = next(token for token in link_tokens if token.endswith("libmata.a"))
    symbols = subprocess.run(["nm", "--defined-only", "-g", library], check=True, capture_output=True, text=True).stdout.split()
    names = sorted({symbol for symbol in symbols if symbol.startswith("_ZN4mata3nfa6reduceERKNS0_3NfaE")})
    if len(names) != 1:
        raise SystemExit(f"expected one mata::nfa::reduce in {library}, found {names}")
    return names[0]


def main():
    args = parse_arguments()
    build_dir = benchlib.REPO / "build" / args.preset
    variant_dir = build_dir / "variants" / args.name
    variant_dir.mkdir(parents=True, exist_ok=True)
    entries = {entry["file"]: entry for entry in json.loads((build_dir / "compile_commands.json").read_text())}

    # the sources are prepared outside the repository (see prepare_sources), the objects go into variant_dir
    with tempfile.TemporaryDirectory() as temporary:
        source_dir = Path(temporary)
        sources = prepare_sources(args.replace, args.patch, source_dir)
        compiles, replaced_objects = [], {}
        for source in sources:
            entry = entries[str(benchlib.REPO / source)]
            output = variant_dir / (Path(source).stem + ".o")
            compiles.append(compile_command(entry, source_dir / source, output, shlex.split(args.cxxflags)))
            replaced_objects[object_in_link(entry, build_dir)] = output
        extra = []
        if args.reduce_log:
            symbol = reduce_symbol(link_command(build_dir, {}, "unused", []))
            # the wrapper needs the include paths of the noodler sources (mata), regex.cpp has them
            regex_entry = entries[str(benchlib.REPO / "src/smt/theory_str_noodler/regex.cpp")]
            wrapper_object = variant_dir / "reduce_wrap.o"
            compiles.append(compile_command(regex_entry, WRAPPER, wrapper_object, [f'-DREDUCE_SYMBOL="{symbol}"']))
            extra = [str(wrapper_object), f"-Wl,--wrap={symbol}"]
        # a compilation takes about 1-2 GB of memory
        with ThreadPoolExecutor(max_workers=4) as pool:
            list(pool.map(lambda command: run(command, cwd=build_dir), compiles))
    run(link_command(build_dir, replaced_objects, variant_dir / "z3", extra), cwd=build_dir)
    print(variant_dir / "z3")


if __name__ == "__main__":
    main()
