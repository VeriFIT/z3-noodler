---
title: Usage
---

[Home](index.md) · [Installation](installation.md) · [Usage](usage.md) · [Publications](publications.md) · [Playground](playground/)

# Usage

Z3-Noodler is used like Z3: it reads SMT-LIB 2 and accepts Z3's command-line options and parameters. The examples assume the binary is installed as `z3-noodler` ([Installation](installation.md)); after a build from source it is `build/z3`.

## Running the solver

Pass an SMT-LIB 2 file and options on the command line, or read the input from standard input with `-smt2 -in`:

```console
$ z3-noodler example.smt2
$ z3-noodler model=true example.smt2
$ z3-noodler -smt2 -in < example.smt2
```

| Option | Effect |
|---|---|
| `model=true` | Enable model generation (see [Models](#models)). |
| `-smt2 -in` | Read SMT-LIB 2 from standard input. |
| `-st` | Print statistics after the answers (see [Statistics](#statistics)). |
| `-T:N` | Hard timeout of *N* seconds. The solver stops and prints `timeout`. |
| `-t:N` or `timeout=N` | Soft timeout of *N* milliseconds for each `check-sat`. A query that runs out of time gives `unknown`. |
| `-memory:N` | Limit the virtual memory to *N* megabytes. |
| `-version` | Print the version of Z3 that Z3-Noodler is based on and the commits of Z3-Noodler and Mata. |
| `-pm:smt` | List the parameters of the `smt` module, including all [Z3-Noodler options](#options). `-p` lists all parameters and `-pd` describes them. |

## Models

`(get-model)` and `(get-value ...)` need model generation, which is off by default. Turn it on with `model=true` on the command line or with `(set-option :produce-models true)` at the top of the input. Without it, `(get-model)` prints an error:

```console
$ z3-noodler example.smt2
sat
(error "line 8 column 10: model is not available, did you forget to enable model generation with ''model=true'?")
```

## Statistics

`-st` prints Z3's statistics after the answers, together with Z3-Noodler's counters of the [decision procedures](index.md#how-it-works) that ran. Here, the stabilization procedure solved the formula:

```console
$ z3-noodler model=true -st example.smt2
sat
(
  ...
)
(:added-eqs                         37
 ...
 :noodler-final_checks              1
 ...
 :str-num-proc-stabilization-finish 1
 :str-num-proc-stabilization-start  1
 ...
 :total-time                        0.02)
```

## Input

### Logics

The logics `QF_S`, `QF_SLIA` and `QF_SNIA` select Z3-Noodler together with Z3's arithmetic solver. Z3-Noodler is also the string solver when the input has no `set-logic` or combines strings with Z3's other theories. Inputs with sequences of other sorts than characters, e.g. `(Seq Int)`, are solved entirely by Z3's own sequence solver.

### String functions

Z3-Noodler supports the functions of the [SMT-LIB theory of strings](https://smt-lib.org/theories-UnicodeStrings.shtml):

- **strings:** `str.++`, `str.len`, `str.at`, `str.substr`, `str.prefixof`, `str.suffixof`, `str.contains`, `str.indexof`, `str.replace`, `str.replace_all`, `str.replace_re`, `str.replace_re_all`, `str.<`, `str.<=`, `str.is_digit`, `str.to_code`, `str.from_code`, `str.to_int`, `str.from_int`;
- **regular expressions:** `str.in_re`, `str.to_re`, `re.++`, `re.*`, `re.+`, `re.opt`, `re.range`, `re.union`, `re.inter`, `re.comp`, `re.diff`, `re.loop`, `re.^`, `re.all`, `re.allchar`, `re.none`.

Not every formula can be decided, so the answer can be `unknown`. For example, string-integer conversions are handled precisely when the converted strings can take only finitely many values; otherwise Z3-Noodler uses an underapproximation that bounds their length.

In standard double-quoted string literals, write non-ASCII characters as `\u{...}` escapes (e.g. `"\u{10c}"` for Č). Raw UTF-8 characters are read byte by byte.

### Incremental solving and unsat cores

`push`/`pop`, named assertions and unsat cores work as in Z3:

```lisp
(set-option :produce-unsat-cores true)
(set-logic QF_SLIA)
(declare-const x String)
(assert (! (str.in_re x (re.+ (str.to_re "ab"))) :named a1))
(push 1)
(assert (! (= (str.len x) 5) :named a2))
(check-sat)
(get-unsat-core)
(pop 1)
(assert (= (str.len x) 6))
(check-sat)
```

```console
$ z3-noodler incremental.smt2
unsat
(a1 a2)
sat
```

## Additional functions

Z3-Noodler adds these functions to SMT-LIB (all details are in [ADDITIONAL_FUNCTIONS.md](https://github.com/VeriFIT/z3-noodler/blob/devel/ADDITIONAL_FUNCTIONS.md)):

| Function | Meaning |
|---|---|
| `(str.to_lower s)`, `(str.to_upper s)` | Converts ASCII letters to lower/upper case (as in cvc5). |
| `(str.trim s)` | Removes ASCII whitespace (characters 0x09-0x0D and 0x20) at both ends. |
| `(str.update s i t)` | Overwrites `s` with `t` from index `i`; the length of `s` stays the same (as in cvc5). |
| `(str.delete s i n)` | Deletes `n` characters of `s` from index `i`. |
| `(str.to_real s)` | The non-negative decimal number in `s` (digits with at most one `.`), or `-1.0` if `s` is not one. |
| `(str.from_real r n)` | `r` written with `n` decimal places (the rest is cut off); `""` if `r` or `n` is negative. |
| `(re.from_ecma2020 'pattern')` | A regular expression given as an ECMAScript 2020 pattern. |
| `RatRel`, `str.in_rat`, `rat.*` | Rational relations: constraints given by finite transducers. |

The string functions:

```lisp
(declare-const x String)
(assert (= (str.to_upper x) "HELLO"))
(assert (str.prefixof "he" x))
(assert (not (= x "hello")))
(check-sat)
(get-value (x
            (str.to_lower "aBcD")
            (str.trim "   aa  ")
            (str.update "123456" 2 "ab")
            (str.delete "AAxxxxBB" 2 4)
            (str.to_real "45.62")
            (str.from_real 3.14159 2)))
```

```console
$ z3-noodler model=true functions.smt2
sat
((x "heLLO")
 ((str.to_lower "aBcD") "abcd")
 ((str.trim "   aa  ") "aa")
 ((str.update "123456" 2 "ab") "12ab56")
 ((str.delete "AAxxxxBB" 2 4) "AABB")
 ((str.to_real "45.62") (/ 2281.0 50.0))
 ((str.from_real 3.14159 2) "3.14"))
```

### ECMAScript regular expressions

`re.from_ecma2020` supports character classes, anchors, (lazy) quantifiers, groups, named groups, backreferences, lookahead and lookbehind, `\b` and `\u{...}`. Write the pattern in single quotes, `'...'`: then backslashes and non-ASCII characters are taken as written (in a double-quoted SMT-LIB string, `"\\d"` stays a backslash pair).

```lisp
(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.from_ecma2020 '(a*b)\1')))
(assert (> (str.len x) 3))
(assert (str.in_re y (re.from_ecma2020 '^\d{3}-\d{4}$')))
(check-sat)
(get-value (x y))
```

```console
$ z3-noodler model=true ecma.smt2
sat
((x "aabaab")
 (y "000-0000"))
```

By default, the whole string must match the pattern, as in [OSTRICH](https://github.com/uuverifiers/ostrich/). With `smt.str.ecma_engine_semantics=true`, a match anywhere in the string is enough, as in an ECMAScript regex engine: `(str.in_re "order 42 shipped" (re.from_ecma2020 '[0-9]+'))` is `unsat` by default and `sat` with the option.

### Rational relations (transducers)

A `RatRel` is a relation between strings given by a finite transducer. `(str.to_rat s t)` relates `s` to `t`, `(rat.identity r)` relates every string of the regular expression `r` to itself, and relations are combined with `rat.++`, `rat.union`, `rat.*`, `rat.+`, `rat.opt`, `rat.compose`, `rat.invert`, `rat.left_extend` and `rat.right_extend` (`rat.none` is the empty relation). `(str.in_rat s t R)` says that `s` and `t` are related by `R`. This relation replaces every `a` by `b`:

```lisp
(declare-const a_to_b RatRel)
(assert (= a_to_b
  (rat.* (rat.union
    (str.to_rat "a" "b")
    (rat.identity (re.diff re.allchar (str.to_re "a")))))))
(declare-const s String)
(assert (str.in_rat "asbabaa" s a_to_b))
(check-sat)
(get-value (s))
```

```console
$ z3-noodler model=true rat.smt2
sat
((s "bsbbbbb"))
```

## Options

Z3-Noodler's options are in Z3's `smt` module. Give them on the command line as `smt.str.<name>=<value>`, or in the input as `(set-option :smt.str.<name> <value>)`:

```console
$ z3-noodler smt.str.ecma_engine_semantics=true input.smt2
```

- `smt.str.ecma_engine_semantics` (default `false`): match `re.from_ecma2020` patterns anywhere in the string, as an ECMAScript regex engine does.
- `smt.str.underapprox` (default `true`): use underapproximation.
- `smt.str.underapprox_length` (default `5`): maximum length of digit words used to underapproximate `str.from_int`/`str.to_int`.
- `smt.str.enable_warnings` (default `false`): raise an error instead of answering `unknown` when the string solver reaches an error state; useful for bug reports.
- `smt.string_solver` (default `noodler`): with `seq`, Z3's own string solver is used instead of Z3-Noodler, e.g. to compare the two.

Z3's options `model` and `timeout` are described in [Running the solver](#running-the-solver).

The following options switch individual techniques on or off, e.g. for experiments:

- `smt.str.try_nielsen` (default `true`): use Nielsen reduction for quadratic formulas.
- `smt.str.try_length_proc` (default `true`): use the length-based decision procedure.
- `smt.str.try_membership_heur` (default `true`): use membership heuristics.
- `smt.str.try_unary_proc` (default `true`): use the procedure for unary alphabets.
- `smt.str.try_premature_length_checks` (default `true`): check length constraints in the main decision procedure before a solution is found, to skip unsatisfiable subtrees.
- `smt.str.postpone_diseqs_stabilization` (default `true`): postpone disequations in stabilization and try a length-only underapproximation first.
- `smt.str.loop_protect` (default `true`): use loop protection.
- `smt.str.preprocess_red` (default `false`): reduce automata eagerly during preprocessing.
- `smt.str.preprocess_nft` (default `true`): use the preprocessing rule that removes transducers.
- `smt.str.homomorphism_heuristic` (default `true`): use the heuristic for homomorphic transducers in noodlification.
- `smt.str.ca_constr` (default `false`): use counter automata for extended string constraints.

`z3-noodler -pm:smt` lists all of them with their descriptions.
