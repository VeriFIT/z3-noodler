---
---

[Home](index.md) · [Installation](installation.md) · [Usage](usage.md) · [Publications](publications.md) · [Playground](playground/)

**Z3-Noodler** is an SMT solver for string constraints such as those that occur in symbolic execution and analysis of programs, reasoning about configuration files of cloud services and smart contracts. It is a fork of [Z3](https://github.com/Z3Prover/z3) in which the solver for the theory of strings is replaced by an automata-based one, with automata handled by the [Mata](https://github.com/VeriFIT/mata) library.

Z3-Noodler won the QF_Strings division of the SMT-COMP Single Query Track in [2024](https://smt-comp.github.io/2024/results/qf_strings-single-query) and [2026](https://smt-comp.github.io/2026/results/qf_strings-single-query).

**[Try it in your browser](playground/)**: the solver runs on your machine via WebAssembly, so your input is not sent anywhere. Binaries for Linux and macOS are on the [latest release](https://github.com/VeriFIT/z3-noodler/releases/latest) page; see [Installation](installation.md).

## How it works

Z3-Noodler keeps Z3's core: its rewriter simplifies the input, and its linear integer arithmetic (LIA) solver handles lengths. The string solver reduces a conjunction of string constraints to a LIA formula over string lengths.

- **Stabilization.** The main decision procedure represents the language of every string variable by a nondeterministic finite automaton and refines the languages according to the word equations until they are *stable*: for every equation, the concatenations of the languages of its two sides are equal. The refinement is done by *noodlification*, an automata operation that generates the feasible alignments of variables. Length constraints built from the stable languages then go to the LIA solver.
- **Completeness.** The procedure is complete for chain-free combinations of equations, length and regular constraints together with unrestricted disequations, the largest known decidable fragment of these types of constraints.
- **A portfolio of procedures.** Based on the features of the input formula, Z3-Noodler can also use Nielsen transformation for quadratic equations, a length-based procedure for large systems of equations, eager automata reduction for difficult regular constraints, and a procedure for unary alphabets.
- **Extended constraints.** String-integer conversions, position constraints such as ¬`str.contains`, and `str.replace_all` / `str.replace_re_all` (through transducers) are solved on top of stabilization.

## Features

- The SMT-LIB theory of strings, with model generation.
- Extensions beyond SMT-LIB: ECMAScript 2020 regular expressions (with capture groups, backreferences and lookarounds), `str.to_lower`, `str.to_upper`, `str.trim`, `str.update`, `str.delete`, string-real conversions and user-defined finite transducers ([details](usage.md#additional-functions)).
- A drop-in replacement for Z3: the same command line, SMT-LIB front end and parameters. Z3's other theories, incremental solving (`push`/`pop`) and unsat cores keep working.

## Quick example

Find strings *x* and *y* such that *x*`ab` = `ba`*y*, *x* is in (`ba`)<sup>+</sup> and *y* is longer than 4:

```lisp
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x "ab") (str.++ "ba" y)))
(assert (str.in_re x (re.+ (str.to_re "ba"))))
(assert (> (str.len y) 4))
(check-sat)
(get-model)
```

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

Continue with [Installation](installation.md) and [Usage](usage.md), or paste the example into the [playground](playground/).

## Links

- Source code: [VeriFIT/z3-noodler](https://github.com/VeriFIT/z3-noodler) on GitHub
- Questions and bug reports: [Issues](https://github.com/VeriFIT/z3-noodler/issues) and [Discussions](https://github.com/VeriFIT/z3-noodler/discussions)
- [Mata](https://github.com/VeriFIT/mata), the automata library behind Z3-Noodler
- The [SMT-LIB theory of strings](https://smt-lib.org/theories-UnicodeStrings.shtml)

## Authors

Vojtěch Havlena, Juraj Síč, Yu-Fang Chen, David Chocholatý, Lukáš Holík, Ondřej Lengál and Michal Hečko. See [Publications](publications.md) for the papers behind Z3-Noodler and how to cite it.

## License

From the [README](https://github.com/VeriFIT/z3-noodler#licensing):

> Z3-Noodler is licensed under the MIT License for general use (see [LICENSE.md](https://github.com/VeriFIT/z3-noodler/blob/devel/LICENSE.md)).
> However, use of this software, or any derivative work, as a participant in the SMT-COMP competition requires a separate Competition Use License from the copyright holder.
> For competitor licensing requests, contact the authors.
>
> Z3-Noodler is a derivative work of the SMT solver Z3.
> The original SMT solver Z3 from the [Z3 repository](https://github.com/Z3Prover/z3) is licensed under the MIT License. See [LICENSE_Z3.txt](https://github.com/VeriFIT/z3-noodler/blob/devel/LICENSE_Z3.txt).
