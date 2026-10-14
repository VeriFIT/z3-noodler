---
title: Installation
---

[Home](index.md) · [Installation](installation.md) · [Usage](usage.md) · [Publications](publications.md) · [Playground](playground/)

# Installation

There are four ways to run Z3-Noodler: a prebuilt binary, a build from source, a Docker image built from source, or the [playground](playground/) in your browser. There are no Python or npm packages: `pip install z3-solver` and `npm install z3-solver` install the upstream Z3, without Z3-Noodler.

## Prebuilt binaries

Every [release](https://github.com/VeriFIT/z3-noodler/releases/latest) comes with binaries for Linux and macOS. Each one is a single executable; Z3 and Mata are linked in.

| System | Release asset |
|---|---|
| Linux, x86-64 | `z3-noodler-ubuntu-24.04-x86_64-shared` |
| macOS 26 or newer, Apple Silicon | `z3-noodler-macos-15-arm64-shared` |
| macOS 15 or newer, Intel | `z3-noodler-macos-15-intel-x86_64-shared` |

There are no Windows binaries.

### Linux

The binary needs glibc 2.38 or newer and the C++ runtime of GCC 13.2 or newer, for example Ubuntu 24.04 (Ubuntu 22.04 is too old). Download the latest release and check that it runs:

```console
$ curl -fL -o z3-noodler https://github.com/VeriFIT/z3-noodler/releases/latest/download/z3-noodler-ubuntu-24.04-x86_64-shared
$ chmod +x z3-noodler
$ ./z3-noodler -version
```

`-version` prints the version of Z3 that Z3-Noodler is based on and the commits of Z3-Noodler and Mata it was built from.

To call it from anywhere, move it to a directory on your `PATH`. The name `z3-noodler` keeps it apart from a system `z3`:

```console
$ mkdir -p ~/.local/bin && mv z3-noodler ~/.local/bin/
```

### macOS

```console
$ # Apple Silicon (macOS 26 or newer)
$ curl -fL -o z3-noodler https://github.com/VeriFIT/z3-noodler/releases/latest/download/z3-noodler-macos-15-arm64-shared
$ # Intel (macOS 15 or newer)
$ curl -fL -o z3-noodler https://github.com/VeriFIT/z3-noodler/releases/latest/download/z3-noodler-macos-15-intel-x86_64-shared
$ chmod +x z3-noodler
$ ./z3-noodler -version
```

The binaries are not notarized. If you download one with a browser instead of `curl`, macOS may refuse to run it; `xattr -d com.apple.quarantine z3-noodler` removes the quarantine flag that the browser sets.

### Check the installation

Save the [quick example](index.md#quick-example) as `example.smt2` and run:

```console
$ z3-noodler model=true example.smt2
sat
(
  (define-fun x () String
    "bababa")
  (define-fun y () String
    "babaab")
)
```

## Build from source

Requirements:

- CMake 3.16 or newer and a C++20 compiler (GCC 13 on Ubuntu 24.04 and Apple Clang on macOS are used in CI),
- Python 3 (used by the build),
- git and network access when running `cmake`: CMake downloads the version of [Mata](https://github.com/VeriFIT/mata) that Z3-Noodler needs and builds it too. If Mata is already installed, that installation is used instead.

On Ubuntu, `sudo apt-get install -y git cmake build-essential python3` installs everything. On macOS, install the Xcode command line tools (`xcode-select --install`) and CMake (e.g. `brew install cmake`).

```console
$ git clone https://github.com/VeriFIT/z3-noodler.git
$ mkdir z3-noodler/build
$ cd z3-noodler/build
$ cmake -DCMAKE_BUILD_TYPE=Release ..
$ make -j"$(nproc)"
$ ./z3 -version
```

On macOS, use `make -j"$(sysctl -n hw.ncpu)"`. The solver is `build/z3`. Always pass `-DCMAKE_BUILD_TYPE=Release`: without it, CMake makes a `RelWithDebInfo` build. Only the CMake build includes Z3-Noodler; Z3's other build methods (e.g. `scripts/mk_make.py`) do not.

### Tests

The tests use [Catch2](https://github.com/catchorg/Catch2) v3, which must be installed *before* `cmake` runs (`sudo apt-get install -y catch2` on Ubuntu, `brew install catch2` on macOS). If you install it later, run `cmake ..` again. The tests must be run from the build directory:

```console
$ make -j"$(nproc)" test-noodler
$ ./test-noodler
```

### Bindings for other languages

The CMake build also produces Z3's library `libz3` with Z3-Noodler as its string solver, and it can build Z3's bindings, e.g. for Python with `-DZ3_BUILD_PYTHON_BINDINGS=ON`; see Z3's [README-CMake.md](https://github.com/VeriFIT/z3-noodler/blob/devel/README-CMake.md).

## Docker

[`docker/z3-noodler.Dockerfile`](https://github.com/VeriFIT/z3-noodler/blob/devel/docker/z3-noodler.Dockerfile) builds Z3-Noodler from source in a Debian container. No image is published, so build it first. It builds the current `devel` branch from GitHub, not your checkout or a release. In a checkout of the repository:

```console
$ docker build -t z3-noodler -f docker/z3-noodler.Dockerfile .
```

Run it on `example.smt2` in the current directory, or on standard input:

```console
$ docker run --rm -v "$PWD":/work --entrypoint /z3-noodler/build/z3 z3-noodler model=true /work/example.smt2
$ docker run --rm -i --entrypoint /z3-noodler/build/z3 z3-noodler -smt2 -in < example.smt2
```

## In the browser

The [playground](playground/) runs Z3-Noodler in your browser via WebAssembly; nothing is installed and your input is not sent anywhere. It is built every night from the `devel` branch, so it can be newer than the latest release (the page shows the commit). It is meant for trying things out:

- it is single-threaded, can use at most 4 GB of memory and is bound by the browser's stack limit (very deeply nested formulas fail),
- it is about 1.5-2 times slower than the native binary,
- set time limits in the *Timeout* field; the `-T:` option does not work there.

Other options, e.g. `smt.str.ecma_engine_semantics=true`, go to the *Extra options* field.
