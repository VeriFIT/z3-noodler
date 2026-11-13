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

from __future__ import annotations

import argparse
import json
import shlex
import shutil
import subprocess
import tempfile
from collections.abc import Sequence
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
REPO = TOOLS.parent
WRAPPER = TOOLS / "instrumentation" / "reduce_wrap.cpp"
GUARD_FLAG_PATCH = TOOLS / "instrumentation" / "guard-flag.patch"

# The source whose compile flags (the include paths of mata) the wrapper is compiled with.
WRAPPER_FLAGS_SOURCE = "src/smt/theory_str_noodler/regex.cpp"

# The mangled name of mata::nfa::reduce starts with this: the name of the function and its first parameter (const Nfa&).
REDUCE_SYMBOL_PREFIX = "_ZN4mata3nfa6reduceERKNS0_3NfaE"

# A compilation takes about 1-2 GB of memory, so only this many of them run at once.
PARALLEL_COMPILATIONS = 4

# A command with its arguments, as subprocess takes it.
Command = list[str]

# An entry of compile_commands.json, with the keys "file" (the source), "command" (how it is compiled) and "output" (the object).
CompileEntry = dict[str, str]


def parse_arguments() -> argparse.Namespace:
    """The command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument("name", help="name of the variant (its directory in build/PRESET/variants)")
    parser.add_argument("--preset", default="release", help="the build to reuse: build/PRESET (default: release)")
    parser.add_argument(
        "--patch",
        action="append",
        default=[],
        type=Path,
        help="apply a patch with repository-relative paths (repeatable)",
    )
    parser.add_argument("--reduce-log", action="store_true", help="link the reduce wrapper and apply guard-flag.patch")

    return parser.parse_args()


# ---------------------------------------------------------------------------------------------------------------------------------
# running commands


def run(command: Command, cwd: Path) -> None:
    """Runs a command in the directory cwd, failing on a non-zero exit code."""
    subprocess.run(command, cwd=cwd, check=True)


def output_of(command: Command, cwd: Path | None = None) -> str:
    """Runs a command, failing on a non-zero exit code, and returns its standard output."""
    finished = subprocess.run(command, cwd=cwd, check=True, capture_output=True, text=True)
    return finished.stdout


def run_in_parallel(commands: list[Command], cwd: Path) -> None:
    """Runs the commands in the directory cwd, PARALLEL_COMPILATIONS of them at once, failing if one of them fails."""
    with ThreadPoolExecutor(max_workers=PARALLEL_COMPILATIONS) as pool:
        started = [pool.submit(run, command, cwd) for command in commands]

        # result() waits for the command and raises its error if the command failed.
        for command_run in started:
            command_run.result()


# ---------------------------------------------------------------------------------------------------------------------------------
# patched copies of the sources


def sources_of_patch(patch: Path, source_dir: Path) -> list[str]:
    """The repository-relative paths of the sources that a patch changes."""
    # git apply --numstat prints one line per source: the added lines, the removed lines and the path, separated by tabs.
    numstat = output_of(["git", "apply", "--numstat", str(patch)], cwd=source_dir)
    return [line.split("\t")[2] for line in numstat.splitlines()]


def apply_patch(patch: Path, source_dir: Path, patched_sources: set[str]) -> bool:
    """Applies a patch to copies of the sources in source_dir and returns whether it applied.

    patched_sources are the repository-relative paths of the sources that are already copied to source_dir.
    A source that the patch changes is copied from the repository first, unless it is already there, and added to patched_sources.
    So several patches of one source apply one after another.
    """
    # Copy the sources that no earlier patch changed.
    for source in sources_of_patch(patch, source_dir):
        if source in patched_sources:
            continue

        copy = source_dir / source
        copy.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(REPO / source, copy)
        patched_sources.add(source)

    # git apply runs in source_dir, which is outside the repository, so it takes the paths of the patch as relative to source_dir.
    # A patch that does not apply is not an error here: the exit code tells the caller.
    applied = subprocess.run(["git", "apply", str(patch)], cwd=source_dir, check=False)
    return applied.returncode == 0


def patch_sources(patches: list[Path], with_guard_flag: bool, source_dir: Path) -> set[str]:
    """Applies the patches to copies of the sources in source_dir and returns the repository-relative paths of the patched sources.

    With with_guard_flag, the guard-flag patch is applied after the given patches.
    """
    patched_sources: set[str] = set()

    # The given patches must apply.
    for patch in patches:
        if not apply_patch(patch.resolve(), source_dir, patched_sources):
            raise SystemExit(f"{patch} does not apply")

    # The guard-flag patch is skipped for sources without today's regex::should_reduce.
    if with_guard_flag and not apply_patch(GUARD_FLAG_PATCH, source_dir, patched_sources):
        print(
            f"{GUARD_FLAG_PATCH.name} does not apply: no reduction is marked as guarded unless a patch sets reduce_guarded"
        )

    return patched_sources


# ---------------------------------------------------------------------------------------------------------------------------------
# the compile commands


def read_compile_entries(build_dir: Path) -> dict[str, CompileEntry]:
    """The entries of compile_commands.json of the build, by the absolute path of their source."""
    entries = json.loads((build_dir / "compile_commands.json").read_text())
    return {entry["file"]: entry for entry in entries}


def compile_command(entry: CompileEntry, source: Path, output: Path, extra_flags: Sequence[str] = ()) -> Command:
    """The command of a compile_commands.json entry, changed to compile source into output, with extra flags."""
    tokens = shlex.split(entry["command"])

    # The object follows -o and the source follows -c.
    tokens[tokens.index("-o") + 1] = str(output)
    tokens[tokens.index("-c") + 1] = str(source)

    # Quoted includes of the original source resolve from its directory, which the copy is not in.
    original_directory = Path(entry["file"]).parent
    return tokens + [f"-I{original_directory}", *extra_flags]


def object_in_link_command(entry: CompileEntry, build_dir: Path) -> str:
    """The object of a compile_commands.json entry as the link command of the build names it: relative to the build directory."""
    built_object = Path(entry["output"])
    if built_object.is_absolute():
        built_object = built_object.relative_to(build_dir)
    return str(built_object)


# ---------------------------------------------------------------------------------------------------------------------------------
# the link command


def z3_link_command(build_dir: Path) -> Command:
    """The command that links z3 in the build."""
    # With -s, ninja prints only the last command that builds z3, which is the link.
    commands = output_of(["ninja", "-C", str(build_dir), "-t", "commands", "-s", "z3"])
    tokens = shlex.split(commands.strip().splitlines()[-1])

    # CMake wraps the command as ": && COMMAND && :".
    if tokens[:2] == [":", "&&"] and tokens[-2:] == ["&&", ":"]:
        tokens = tokens[2:-2]

    return tokens


def variant_link_command(
    z3_link: Command,
    replaced_objects: dict[str, Path],
    output: Path,
    extra_arguments: Sequence[str] = (),
) -> Command:
    """The link command of z3 (z3_link), changed to link a variant into output.

    replaced_objects maps objects of the build, as z3_link names them, to the objects that are linked in their place.
    extra_arguments are added before the libraries.
    """
    tokens = list(z3_link)

    # The patched objects in place of the original ones.
    for original, replacement in replaced_objects.items():
        tokens[tokens.index(original)] = str(replacement)

    # The dependency file of the link belongs to the build, so the variant does not write it.
    if "-Xlinker" in tokens:
        index = tokens.index("-Xlinker")
        if tokens[index + 1].startswith("--dependency-file="):
            del tokens[index : index + 2]

    # The output follows -o, and the libraries follow the output.
    index = tokens.index("-o")
    return tokens[:index] + ["-o", str(output), *extra_arguments] + tokens[index + 2 :]


def reduce_symbol(z3_link: Command) -> str:
    """The mangled name of mata::nfa::reduce in the mata library that z3_link links."""
    library = next(token for token in z3_link if token.endswith("libmata.a"))

    # nm prints the symbols that the library defines, and the name of a symbol is one word.
    words = output_of(["nm", "--defined-only", "-g", library]).split()
    names = sorted({word for word in words if word.startswith(REDUCE_SYMBOL_PREFIX)})

    if len(names) != 1:
        raise SystemExit(f"expected one mata::nfa::reduce in {library}, found {names}")
    return names[0]


# ---------------------------------------------------------------------------------------------------------------------------------


def main() -> None:
    """Compiles the patched sources (and the wrapper), then links the variant."""
    args = parse_arguments()

    build_dir = REPO / "build" / args.preset
    variant_dir = build_dir / "variants" / args.name
    variant_dir.mkdir(parents=True, exist_ok=True)

    compile_entries = read_compile_entries(build_dir)
    z3_link = z3_link_command(build_dir)

    compile_commands: list[Command] = []
    replaced_objects: dict[str, Path] = {}
    extra_link_arguments: list[str] = []

    # The patched copies of the sources are in a temporary directory, which is removed when they are compiled.
    with tempfile.TemporaryDirectory() as temporary:
        source_dir = Path(temporary)
        patched_sources = patch_sources(args.patch, args.reduce_log, source_dir)

        # Each patched source is compiled into variant_dir, and its object is linked in place of the object of the build.
        for source in sorted(patched_sources):
            entry = compile_entries[str(REPO / source)]
            patched_object = variant_dir / (Path(source).stem + ".o")

            compile_commands.append(compile_command(entry, source_dir / source, patched_object))
            replaced_objects[object_in_link_command(entry, build_dir)] = patched_object

        # The wrapper is linked with --wrap, so that the calls of reduce from z3 go through it.
        if args.reduce_log:
            symbol = reduce_symbol(z3_link)
            wrapper_object = variant_dir / "reduce_wrap.o"
            wrapper_entry = compile_entries[str(REPO / WRAPPER_FLAGS_SOURCE)]
            symbol_flag = f'-DREDUCE_SYMBOL="{symbol}"'

            compile_commands.append(compile_command(wrapper_entry, WRAPPER, wrapper_object, [symbol_flag]))
            extra_link_arguments = [str(wrapper_object), f"-Wl,--wrap={symbol}"]

        run_in_parallel(compile_commands, build_dir)

    variant = variant_dir / "z3"
    run(variant_link_command(z3_link, replaced_objects, variant, extra_link_arguments), cwd=build_dir)
    print(variant)


if __name__ == "__main__":
    main()
