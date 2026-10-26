#!/usr/bin/env -S just --justfile

# Root justfile of Z3-Noodler. Builds are configured out of source in 'build/<MODE>/<CXX>'. Nix recipes live
# in the 'nix' module: list them with 'just --list nix'.

mod nix 'nix/nix.just'

alias b := build
alias t := test
alias r := release
alias rd := release-debuginfo
alias f := nix::fmt
alias c := clean
alias h := help

# Directory with out-of-source CMake builds.
BUILD_ROOT := justfile_directory() / "build"

# Compiler to use. Options: "g++", "clang++", ...
CXX := env("CXX", "g++")

# Build mode used by recipes which do not take one explicitly.
# Options: "debug", "release", "release-debuginfo".
BUILD_MODE := env("BUILD_MODE", "debug")

# Number of cores for parallel compilation.
JOBS := env("JOBS", num_cpus())

# Build and run the Noodler tests (Catch2). Extra ARGS go to Catch2, e.g. 'just test release "[e2e]"'.
[default]
test MODE=BUILD_MODE *ARGS: (configure MODE)
	cmake --build '{{ BUILD_ROOT }}/{{ MODE }}/{{ CXX }}' --parallel '{{ JOBS }}' --target test-noodler
	cd '{{ BUILD_ROOT }}/{{ MODE }}/{{ CXX }}' && ./test-noodler {{ ARGS }}

# Configure the CMake build directory of MODE. Extra ARGS go to CMake.
configure MODE=BUILD_MODE *ARGS:
	cmake -S '{{ justfile_directory() }}' -B '{{ BUILD_ROOT }}/{{ MODE }}/{{ CXX }}' \
		-DCMAKE_CXX_COMPILER='{{ CXX }}' \
		-DCMAKE_BUILD_TYPE='{{ if MODE == "debug" { "Debug" } else if MODE == "release" { "Release" } else if MODE == "release-debuginfo" { "RelWithDebInfo" } else { error("Unknown build mode: " + MODE) } }}' \
		-DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
		{{ ARGS }}

# Build 'z3' and 'libz3' and publish the compilation database at 'build/compile_commands.json'.
build MODE=BUILD_MODE: (configure MODE)
	cmake --build '{{ BUILD_ROOT }}/{{ MODE }}/{{ CXX }}' --parallel '{{ JOBS }}'
	cp -f '{{ BUILD_ROOT }}/{{ MODE }}/{{ CXX }}/compile_commands.json' '{{ BUILD_ROOT }}/compile_commands.json'

# Build in release mode.
release: (build "release")

# Build in release mode with debug information.
release-debuginfo: (build "release-debuginfo")

# Run the built 'z3' binary, e.g. 'just run release model=true formula.smt2'.
run MODE=BUILD_MODE *ARGS:
	'{{ BUILD_ROOT }}/{{ MODE }}/{{ CXX }}/z3' {{ ARGS }}

# Remove the build directories created by the recipes. Other directories in 'build/' are kept.
clean:
	rm -rf '{{ BUILD_ROOT }}/debug' '{{ BUILD_ROOT }}/release' '{{ BUILD_ROOT }}/release-debuginfo' '{{ BUILD_ROOT }}/compile_commands.json'

# Update the flake inputs.
update: nix::update

# List all recipes, including the recipes of all modules.
help:
	@just --list --list-submodules --justfile '{{ justfile() }}'
