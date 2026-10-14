---
title: Publications
---

[Home](index.md) · [Installation](installation.md) · [Usage](usage.md) · [Publications](publications.md) · [Playground](playground/)

# Publications

## How to cite

If you use Z3-Noodler in your work, please cite the tool paper:

> Y.-F. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál and J. Síč. [Z3-Noodler: An Automata-based String Solver](https://doi.org/10.1007/978-3-031-57246-3_2). In *Proc. of TACAS'24*, volume 14570 of LNCS, pages 24-33, 2024. Springer.

{% raw %}
```bibtex
@inproceedings{z3noodler-tacas24,
  author    = {Yu-Fang Chen and David Chocholat{\'y} and Vojt{\v{e}}ch Havlena and Luk{\'a}{\v{s}} Hol{\'i}k and Ond{\v{r}}ej Leng{\'a}l and Juraj S{\'i}{\v{c}}},
  title     = {{Z3-Noodler}: An Automata-based String Solver},
  booktitle = {Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2024)},
  editor    = {Bernd Finkbeiner and Laura Kov{\'a}cs},
  series    = {Lecture Notes in Computer Science},
  volume    = {14570},
  pages     = {24--33},
  publisher = {Springer},
  year      = {2024},
  doi       = {10.1007/978-3-031-57246-3_2}
}
```
{% endraw %}

For the current version of Z3-Noodler, with its portfolio of decision procedures and model generation, please also cite:

> D. Chocholatý, V. Havlena, L. Holík, J. Hranička, O. Lengál and J. Síč. [Z3-Noodler 1.3: Shepherding Decision Procedures for Strings with Model Generation](https://doi.org/10.1007/978-3-031-90653-4_2). In *Proc. of TACAS'25*, volume 15697 of LNCS, pages 23-44, 2025. Springer.

{% raw %}
```bibtex
@inproceedings{z3noodler13-tacas25,
  author    = {David Chocholat{\'y} and Vojt{\v{e}}ch Havlena and Luk{\'a}{\v{s}} Hol{\'i}k and Jan Hrani{\v{c}}ka and Ond{\v{r}}ej Leng{\'a}l and Juraj S{\'i}{\v{c}}},
  title     = {{Z3-Noodler} 1.3: Shepherding Decision Procedures for Strings with Model Generation},
  booktitle = {Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2025)},
  editor    = {Arie Gurfinkel and Marijn Heule},
  series    = {Lecture Notes in Computer Science},
  volume    = {15697},
  pages     = {23--44},
  publisher = {Springer},
  year      = {2025},
  doi       = {10.1007/978-3-031-90653-4_2}
}
```
{% endraw %}

## Papers

- D. Chocholatý, V. Havlena, L. Holík, J. Síč and M. Šedý. [String Solving with Stabilization and Transducers](https://doi.org/10.1007/978-3-032-32526-6_3). In *Proc. of CAV'26*, volume 16683 of LNCS, pages 50-74, 2026. Springer. ([arXiv](https://arxiv.org/abs/2605.14872))
- Y.-F. Chen, V. Havlena, M. Hečko, L. Holík and O. Lengál. [A Uniform Framework for Handling Position Constraints in String Solving](https://doi.org/10.1145/3729273). In *Proc. of PLDI'25*, PACMPL volume 9, pages 550-575, 2025. ACM. ([arXiv](https://arxiv.org/abs/2504.07033))
- D. Chocholatý, V. Havlena, L. Holík, J. Hranička, O. Lengál and J. Síč. [Z3-Noodler 1.3: Shepherding Decision Procedures for Strings with Model Generation](https://doi.org/10.1007/978-3-031-90653-4_2). In *Proc. of TACAS'25*, volume 15697 of LNCS, pages 23-44, 2025. Springer.
- V. Havlena, L. Holík, O. Lengál and J. Síč. [Cooking String-Integer Conversions with Noodles](https://doi.org/10.4230/LIPIcs.SAT.2024.14). In *Proc. of SAT'24*, volume 305 of LIPIcs, pages 14:1-14:19, 2024. Schloss Dagstuhl – Leibniz-Zentrum für Informatik.
- Y.-F. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál and J. Síč. [Z3-Noodler: An Automata-based String Solver](https://doi.org/10.1007/978-3-031-57246-3_2). In *Proc. of TACAS'24*, volume 14570 of LNCS, pages 24-33, 2024. Springer. ([arXiv](https://arxiv.org/abs/2310.08327))
- Y.-F. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál and J. Síč. [Solving String Constraints with Lengths by Stabilization](https://doi.org/10.1145/3622872). In *Proc. of OOPSLA'23*, PACMPL volume 7, pages 2112-2141, 2023. ACM.
- F. Blahoudek, Y.-F. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál and J. Síč. [Word Equations in Synergy with Regular Constraints](https://doi.org/10.1007/978-3-031-27481-7_23). In *Proc. of FM'23*, volume 14000 of LNCS, pages 403-423, 2023. Springer. ([arXiv](https://arxiv.org/abs/2212.02317))

The automata library behind Z3-Noodler:

- D. Chocholatý, T. Fiedor, V. Havlena, L. Holík, M. Hruška, O. Lengál and J. Síč. [Mata: A Fast and Simple Finite Automata Library](https://doi.org/10.1007/978-3-031-57249-4_7). In *Proc. of TACAS'24*, volume 14571 of LNCS, pages 130-151, 2024. Springer. ([arXiv](https://arxiv.org/abs/2310.10136))

## SMT-COMP system descriptions

Short overviews of the solver as it entered the [SMT competition](https://smt-comp.github.io/): [2026](https://github.com/VeriFIT/z3-noodler/blob/devel/doc/noodler/z3-noodler-system-description-2026.pdf), [2025](https://github.com/VeriFIT/z3-noodler/blob/devel/doc/noodler/z3-noodler-system-description-2025.pdf), [2024](https://github.com/VeriFIT/z3-noodler/blob/devel/doc/noodler/z3-noodler-system-description-2024.pdf), [2023](https://github.com/VeriFIT/z3-noodler/blob/devel/doc/noodler/z3-noodler-system-description-2023.pdf).

## BibTeX of the other papers

{% raw %}
```bibtex
@inproceedings{transducers-cav26,
  author    = {David Chocholat{\'y} and Vojt{\v{e}}ch Havlena and Luk{\'a}{\v{s}} Hol{\'i}k and Juraj S{\'i}{\v{c}} and Michal {\v{S}}ed{\'y}},
  title     = {String Solving with Stabilization and Transducers},
  booktitle = {Computer Aided Verification (CAV 2026)},
  editor    = {Eva Darulova and Anthony W. Lin and Philipp R{\"u}mmer},
  series    = {Lecture Notes in Computer Science},
  volume    = {16683},
  pages     = {50--74},
  publisher = {Springer},
  year      = {2026},
  doi       = {10.1007/978-3-032-32526-6_3}
}

@article{position-pldi25,
  author    = {Yu-Fang Chen and Vojt{\v{e}}ch Havlena and Michal He{\v{c}}ko and Luk{\'a}{\v{s}} Hol{\'i}k and Ond{\v{r}}ej Leng{\'a}l},
  title     = {A Uniform Framework for Handling Position Constraints in String Solving},
  journal   = {Proceedings of the ACM on Programming Languages},
  volume    = {9},
  number    = {PLDI},
  pages     = {550--575},
  year      = {2025},
  publisher = {ACM},
  doi       = {10.1145/3729273}
}

@inproceedings{conversions-sat24,
  author    = {Vojt{\v{e}}ch Havlena and Luk{\'a}{\v{s}} Hol{\'i}k and Ond{\v{r}}ej Leng{\'a}l and Juraj S{\'i}{\v{c}}},
  title     = {Cooking String-Integer Conversions with Noodles},
  booktitle = {27th International Conference on Theory and Applications of Satisfiability Testing (SAT 2024)},
  series    = {Leibniz International Proceedings in Informatics (LIPIcs)},
  volume    = {305},
  pages     = {14:1--14:19},
  publisher = {Schloss Dagstuhl -- Leibniz-Zentrum f{\"u}r Informatik},
  year      = {2024},
  doi       = {10.4230/LIPIcs.SAT.2024.14}
}

@article{stabilization-oopsla23,
  author    = {Yu-Fang Chen and David Chocholat{\'y} and Vojt{\v{e}}ch Havlena and Luk{\'a}{\v{s}} Hol{\'i}k and Ond{\v{r}}ej Leng{\'a}l and Juraj S{\'i}{\v{c}}},
  title     = {Solving String Constraints with Lengths by Stabilization},
  journal   = {Proceedings of the ACM on Programming Languages},
  volume    = {7},
  number    = {OOPSLA2},
  pages     = {2112--2141},
  year      = {2023},
  publisher = {ACM},
  doi       = {10.1145/3622872}
}

@inproceedings{synergy-fm23,
  author    = {Franti{\v{s}}ek Blahoudek and Yu-Fang Chen and David Chocholat{\'y} and Vojt{\v{e}}ch Havlena and Luk{\'a}{\v{s}} Hol{\'i}k and Ond{\v{r}}ej Leng{\'a}l and Juraj S{\'i}{\v{c}}},
  title     = {Word Equations in Synergy with Regular Constraints},
  booktitle = {Formal Methods (FM 2023)},
  editor    = {Marsha Chechik and Joost-Pieter Katoen and Martin Leucker},
  series    = {Lecture Notes in Computer Science},
  volume    = {14000},
  pages     = {403--423},
  publisher = {Springer},
  year      = {2023},
  doi       = {10.1007/978-3-031-27481-7_23}
}
```
{% endraw %}
