# Z3-Noodler

[![GitHub tag](https://img.shields.io/github/tag/VeriFIT/z3-noodler.svg)](https://github.com/VeriFIT/z3-noodler)
![Build](https://github.com/VeriFIT/z3-noodler/actions/workflows/build.yml/badge.svg)
![JS Binding](https://github.com/VeriFIT/z3-noodler/actions/workflows/js-binding.yml/badge.svg)

Z3-Noodler is an SMT solver for string constraints such as those that occur in symbolic execution and analysis of programs, 
reasoning about configuration files of cloud services and smart contracts, etc.
Z3-Noodler is based on the SMT solver [Z3 v4.13.4](https://github.com/Z3Prover/z3/releases/tag/z3-4.13.4), in which it replaces the solver for the theory of strings. 
The core of the string solver implements several decision procedures, but mainly it relies on the equation stabilization algorithm (see [Publications](#publications)).

Z3-Noodler utilizes the automata library [Mata](https://github.com/VeriFIT/mata/) for efficient representation of automata and their processing.

For a brief overview of the architecture, see [SMT-COMP'24 Z3-Noodler description](doc/noodler/z3-noodler-system-description-2024.pdf).

[//]: # (TODO: Write the following paragraphs. ## Differences from Z3)

## Building and running

### Dependencies

1) The [Mata](https://github.com/VeriFIT/mata/) library for efficient handling of finite automata. Minimum required version of `mata` is `v1.18.0`.
    ```shell
    git clone 'https://github.com/VeriFIT/mata.git'
    cd mata
    make release
    sudo make install
    ```

    Make sure your system looks for libraries in `/usr/local/include` (where Mata will be installed). For example, MacOS might skip looking for libraries there, so you might need to add these paths by running, for example `xcode-select --install`, as per a [suggestion from StackOverflow](https://stackoverflow.com/a/26265473).

### Building Z3-Noodler

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

To build tests for Z3-Noodler (assuming you have [Catch2](https://github.com/catchorg/Catch2) version 3 installed), run the following 
command.
```shell
make test-noodler
```

### Running Z3-Noodler
To run Z3-Noodler, use:
```shell
cd build/
./z3 <instance_file.smt2> 
```

If you want to get a model for sat instances (using `get-model` or `get-value`), you need to enable model generation:
```shell
cd build/
./z3 model=true <instance_file.smt2> 
```

To run tests for Z3-Noodler, execute
```shell
cd build/
./test-noodler
```

## Publications
- D. Chocholatý, V. Havlena, L. Holík, J. Hranička, O. Lengál, and J. Síč. [Z3-Noodler 1.3: Shepherding Decision Procedures for Strings with Model Generation](https://link.springer.com/chapter/10.1007/978-3-031-90653-4_2). In *Proc. of TACAS'25*, volume 15697 of LNCS, pages 23-44, 2025. Springer.
- V. Havlena, L. Holík, O. Lengál, and J. Síč. [Cooking String-Integer Conversions with Noodles](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.14). In *Proc. of SAT'24*, LIPIcs, Volume 305, pp. 14:1-14:19, 2024. Schloss Dagstuhl – Leibniz-Zentrum für Informatik.
- Y. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál, and J. Síč. [Z3-Noodler: An Automata-based String Solver](https://doi.org/10.1007/978-3-031-57246-3_2). In *Proc. of TACAS'24*, volume 14570 of LNCS, pages 24-33, 2024. Springer. 
- Y. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál, and J. Síč. [Solving String Constraints with Lengths by Stabilization](https://doi.org/10.1145/3622872). In *Proc. of OOPSLA'23*, Volume 7, Issue OOPSLA2, pages  2112–2141, 2023. ACM.
- F. Blahoudek, Y. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál, and J. Síč. [Word Equations in Synergy with Regular Constraints](https://doi.org/10.1007/978-3-031-27481-7_23).  In *Proc. of FM’23*, volume 14000 of LNCS, pages 403–423, 2023. Springer.


## Z3-Noodler source files

The string solver of Z3-Noodler is implemented in [src/smt/theory_str_noodler](src/smt/theory_str_noodler).

Tests for Z3-Noodler are located in [src/test/noodler](src/test/noodler).

## Licensing

Z3-Noodler is licensed under the MIT License. See [LICENSE.md](./LICENSE.md).

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
