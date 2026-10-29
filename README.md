# Z3-Noodler

[![GitHub tag](https://img.shields.io/github/tag/VeriFIT/z3-noodler.svg)](https://github.com/VeriFIT/z3-noodler)
![Build](https://github.com/VeriFIT/z3-noodler/actions/workflows/noodler-build-test.yml/badge.svg)
![JS Binding](https://github.com/VeriFIT/z3-noodler/actions/workflows/noodler-js-binding.yml/badge.svg)

Z3-Noodler is an SMT solver for string constraints such as those that occur in symbolic execution and analysis of programs, 
reasoning about configuration files of cloud services and smart contracts, etc.
Z3-Noodler is based on the SMT solver [Z3 v5.1.0](https://github.com/Z3Prover/z3/releases/tag/z3-5.1.0), in which it replaces the solver for the theory of strings. 
The core of the string solver implements several decision procedures, but mainly it relies on the equation stabilization algorithm (see [Publications](#publications)).

Z3-Noodler utilizes the automata library [Mata](https://github.com/VeriFIT/mata/) for efficient representation of automata and their processing.

For a brief overview of the architecture, see [SMT-COMP'24 Z3-Noodler description](doc/noodler/z3-noodler-system-description-2024.pdf).

## Building and running

### Step 1 (Optional): Install Mata

Z3-Noodler depends on the Mata library for efficient handling of finite automata.

Installing Mata **is not required** to build or run Z3-Noodler.
If Mata is not found on your system, it will be **automatically fetched and built** as part of the Z3-Noodler build process.

However, if you plan to **develop or frequently rebuild Z3-Noodler**, it is recommended to install Mata manually. This avoids repeatedly downloading and rebuilding Mata and significantly speeds up development workflows.

Z3-Noodler needs Mata `v1.32.45-dev.160` (a development tag of Mata, not a release).

To install the version of Mata that Z3-Noodler uses, run:
```shell
git clone --branch v1.32.45-dev.160 'https://github.com/VeriFIT/mata.git'
cd mata
make release
sudo make install
```

Make sure your system looks for libraries in `/usr/local/include` (where Mata will be installed).
On macOS, you may [need to install the Xcode command line tools](https://stackoverflow.com/a/26265473):
```shell
xcode-select --install
```

### Step 2: Build Z3-Noodler

Building requires CMake 3.16 or newer, a C++20 compiler (GCC 13 or newer, or Apple Clang), and Python 3 (used by the build to generate source files).
If Mata is not installed, git and network access are also needed when running `cmake`.

```shell
git clone 'https://github.com/VeriFIT/z3-noodler.git'
mkdir z3-noodler/build
cd z3-noodler/build
cmake -DCMAKE_BUILD_TYPE=Release ..
make
```
See [instructions for building Z3][cmake] for more details.

[visual_studio]: README-Z3.md#building-z3-on-windows-using-visual-studio-command-prompt
[make]: README-Z3.md#building-z3-using-make-and-gccclang
[cmake]: README-Z3.md#building-z3-using-cmake

To build tests for Z3-Noodler, you need [Catch2](https://github.com/catchorg/Catch2) version 3.
Catch2 is detected when `cmake` is run, so install it **before** running `cmake` (or re-run `cmake` after installing it); otherwise, the `test-noodler` target does not exist.
Then, run the following command in the build directory:
```shell
make test-noodler
```

### Alternative: Build with Nix

The repository is a Nix flake, which provides Mata, Catch2, and all build tools:
```shell
nix build                 # Builds and tests Z3-Noodler with GCC; the binary is 'result/bin/z3'.
nix build '.#noodlerClang' # The same with Clang.
nix develop               # Development shell with GCC ('.#clang' for Clang); 'direnv allow' enters it automatically.
nix fmt                   # Formats the Nix files.
```
Inside the development shell, `just` builds and runs the tests in `build/<mode>/<compiler>`, e.g. `just test release`; run `just help` to list all recipes.

### Step 3: Run Z3-Noodler
To run Z3-Noodler on an SMT-LIB instance:
```shell
./z3 <instance_file.smt2> 
```

If you want to get a model for sat instances (using `get-model` or `get-value`), you need to enable model generation:
```shell
./z3 model=true <instance_file.smt2> 
```

With Nix, `nix run` builds Z3-Noodler and runs it, with no clone or manual build needed:
```shell
nix run 'github:VeriFIT/z3-noodler' -- <instance_file.smt2>
nix run 'github:VeriFIT/z3-noodler' -- model=true <instance_file.smt2>
```
In a clone of the repository, use `nix run . -- <instance_file.smt2>`.

To run tests for Z3-Noodler, run the following command in the build directory (the end-to-end tests use the `z3` binary from the current directory):
```shell
./test-noodler
```
To use a `z3` binary from a different location, set `NOODLER_E2E_Z3=/path/to/z3`.

## Additional string functions
Other than the constraints defined in the [SMT-LIB theory of strings](https://smt-lib.org/theories-UnicodeStrings.shtml), Z3-Noodler can handle some additional functions
(defined in [ADDITIONAL_FUNCTIONS.md](ADDITIONAL_FUNCTIONS.md)):
 - `str.to_real`
 - `str.from_real`
 - `str.to_lower`
 - `str.to_upper`
 - `str.update`
 - `str.trim`
 - `str.delete`
 - `re.from_ecma2020` 
 - functions for rational relations (finite transducers)

## Publications
- D. Chocholatý, V. Havlena, L. Holík, J. Síč, and M. Šedý. [String Solving with Stabilization and Transducers](https://doi.org/10.1007/978-3-032-32526-6_3). In *Proc. of CAV'26*, volume 16683 of LNCS, pages 50-74, 2026. Springer.
- Y. Chen, V. Havlena, M.Hečko, L.Holík, and O. Lengál. [A Uniform Framework for Handling Position Constraints in String Solving](https://dl.acm.org/doi/10.1145/3729273). In *Proc. of PLDI'25*, volume 9, pages 550-575, 2025. ACM.
- D. Chocholatý, V. Havlena, L. Holík, J. Hranička, O. Lengál, and J. Síč. [Z3-Noodler 1.3: Shepherding Decision Procedures for Strings with Model Generation](https://link.springer.com/chapter/10.1007/978-3-031-90653-4_2). In *Proc. of TACAS'25*, volume 15697 of LNCS, pages 23-44, 2025. Springer.
- V. Havlena, L. Holík, O. Lengál, and J. Síč. [Cooking String-Integer Conversions with Noodles](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.14). In *Proc. of SAT'24*, LIPIcs, Volume 305, pp. 14:1-14:19, 2024. Schloss Dagstuhl – Leibniz-Zentrum für Informatik.
- Y. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál, and J. Síč. [Z3-Noodler: An Automata-based String Solver](https://doi.org/10.1007/978-3-031-57246-3_2). In *Proc. of TACAS'24*, volume 14570 of LNCS, pages 24-33, 2024. Springer. 
- Y. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál, and J. Síč. [Solving String Constraints with Lengths by Stabilization](https://doi.org/10.1145/3622872). In *Proc. of OOPSLA'23*, Volume 7, Issue OOPSLA2, pages  2112–2141, 2023. ACM.
- F. Blahoudek, Y. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál, and J. Síč. [Word Equations in Synergy with Regular Constraints](https://doi.org/10.1007/978-3-031-27481-7_23).  In *Proc. of FM’23*, volume 14000 of LNCS, pages 403–423, 2023. Springer.


## Z3-Noodler source files

The string solver of Z3-Noodler is implemented in [src/smt/theory_str_noodler](src/smt/theory_str_noodler).

Tests for Z3-Noodler are located in [src/test/noodler](src/test/noodler).

## Licensing

Z3-Noodler is licensed under the MIT License for general use (see [LICENSE.md](./LICENSE.md)).
However, use of this software, or any derivative work, as a participant in the SMT-COMP competition requires a separate Competition Use License from the copyright holder.
For competitor licensing requests, contact the authors.

Z3-Noodler is a derivative work of the SMT solver Z3.
The original SMT solver Z3 from the [Z3 repository](https://github.com/Z3Prover/z3) is licensed under the MIT License. See [LICENSE_Z3.txt](./LICENSE_Z3.txt).

## Original Z3 README

For the original Z3 README, see [README-Z3.md](README-Z3.md).

## Authors
- :envelope: [Vojtěch Havlena](mailto:ihavlena@fit.vut.cz?subject=[GitHub]%20Z3-Noodler),
- :envelope: [Juraj Síč](mailto:sicjuraj@fit.vut.cz?subject=[GitHub]%20Z3-Noodler),
- [Yu-Fang Chen](mailto:yfc@iis.sinica.edu.tw?subject=[GitHub]%20Z3-Noodler),
- [David Chocholatý](mailto:xchoch08@stud.fit.vutbr.cz?subject=[GitHub]%20Z3-Noodler),
- [Lukáš Holík](mailto:holik@fit.vut.cz?subject=[GitHub]%20Z3-Noodler),
- [Ondřej Lengál](mailto:lengal@fit.vut.cz?subject=[GitHub]%20Z3-Noodler),
- [Michal Hečko](mailto:ihecko@fit.vut.cz?subject=[GitHub]%20Z3-Noodler).
