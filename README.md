# Formalizing the Stacks Project in Lean

The [Stacks Project](https://stacks.math.columbia.edu/) is a collaborative, open-source textbook and reference work on algebraic geometry, covering topics from commutative algebra and scheme theory to cohomology and algebraic stacks. It systematically organizes mathematical definitions, lemmas, propositions, and theorems, together with detailed proofs. We are formalizing the [Stacks Project](https://stacks.math.columbia.edu/) in Lean 4 and organizing its mathematical content into **ReasLib**, a shared library of definitions, theorem statements, proofs, and dependencies. **ReasLib currently contains 25,634 Lean source files.**

Our work turns entries from the Stacks Project into reusable Lean definitions and results built on Mathlib. Shared mathematical content is organized by subject, with chapter-based modules retaining their correspondence to the source. The goal is a library that can support further formalization and mathematical work as proofs are completed and definitions and statements are refined. AI-assisted formalization and integration are organized through [Quokka](https://quokka.reaslab.io).

The library is under active development and contains unfinished proofs marked with `sorry`. We welcome downstream use of ReasLib and contributions to fill in the remaining `sorry` placeholders along the way. See [pull requests and merging](#pull-requests-and-merging) to get started.

## Library overview

ReasLib spans algebraic geometry, category theory, algebra, ring theory, topology,
and related areas. Its source files are organized as follows:

| Subject directory | Lean source files | Definitions | Theorems | Source lines |
| --- | ---: | ---: | ---: | ---: |
| [AlgebraicGeometry](ReasLib/AlgebraicGeometry/) | 12,892 | 53,670 | 56,538 | 1,509,581 |
| [CategoryTheory](ReasLib/CategoryTheory/) | 5,293 | 16,479 | 28,484 | 600,724 |
| [Algebra](ReasLib/Algebra/) | 3,248 | 15,454 | 19,451 | 428,092 |
| [RingTheory](ReasLib/RingTheory/) | 2,895 | 6,964 | 13,084 | 287,777 |
| [Topology](ReasLib/Topology/) | 506 | 1,749 | 1,966 | 46,958 |
| [AlgebraicTopology](ReasLib/AlgebraicTopology/) | 369 | 1,570 | 2,814 | 49,527 |
| Other subject directories | 431 | 1,014 | 2,009 | 49,548 |
| **Total** | **25,634** | **96,900** | **124,346** | **2,972,207** |

The repository is organized as follows.

| Path | Contents |
| --- | --- |
| [`ReasLib/`](ReasLib/) | Shared mathematical definitions and results, organized by subject. |
| [`stacks_project/`](stacks_project/) | Chapter-organized checks linking ReasLib declarations to the original Stacks Project entries. |
| [`lakefile.toml`](lakefile.toml) | Library targets, options, and dependency revisions. |
| [`lean-toolchain`](lean-toolchain) | Required Lean toolchain. |

`ReasLib/` contains the mathematical definitions, statements, and proofs, organized
by subject. The check files in `stacks_project/` follow the original Stacks Project
chapter structure and record how its entries correspond to declarations in
ReasLib. They import the relevant library modules and use `#check` to check
declarations against the expected statements. Where present, `@[stacks TAG]`
annotations identify the original entry at `https://stacks.math.columbia.edu/tag/TAG`.

## How to use

### Work with the source locally

To use ReasLib locally, please clone and build the library:

```sh
git clone https://github.com/optpku/stacks.git
cd stacks
lake exe cache get
lake build ReasLib
```

You can also build individual modules and their dependencies. For example, the first command below builds the ReasLib module for the size of schemes. The second builds the check module corresponding to Stacks Project Lemma 3.9.1:

```sh
lake build ReasLib.AlgebraicGeometry.Scheme.Size
lake build stacks_project.Chap03.Lemma_3_9_1
```

### Use ReasLib as a project dependency

In a Lean project using a compatible toolchain and Mathlib revision, add the following to `lakefile.toml`. Replace `<commit-or-tag>` with the revision you intend to use:

```toml
[[require]]
name = "stacks_project"
git = "https://github.com/optpku/stacks.git"
rev = "<commit-or-tag>"
```

Run `lake update stacks_project` to resolve the dependency. The Lake package name is `stacks_project`. Its shared mathematical modules use the `ReasLib` prefix. Use `import ReasLib` to load the main modules together, or import individual modules as needed. Import a specific module to use its declarations:

```lean
import ReasLib.AlgebraicGeometry.Scheme.Size

#check AlgebraicGeometry.Scheme.size
#check AlgebraicGeometry.Scheme.size_eq
```


## Pull requests and merging

We welcome proof completions, corrections to mathematical statements, improvements to shared definitions and theorem statements, and documentation fixes. You may use AI tools when preparing a contribution.

### Preparing a pull request

1. Fork the repository and create a branch for a focused change.
2. Reuse existing Mathlib and ReasLib definitions where possible. Put reusable mathematical content in `ReasLib/`, and maintain the corresponding chapter entry when changing the formalization of a Stacks item. ReasLib modules should remain independent of `stacks_project` chapter modules.
3. Build the changed modules and affected downstream modules. For changes to shared definitions or theorem statements, also run `lake build ReasLib`. Include the commands and results in the PR description, and identify anything you could not check.
4. Open a [pull request](https://github.com/optpku/stacks/pulls) describing the mathematical source, the change, and its effect on existing users.

Please include the following information:

- **Source:** the Stacks tag or other reference, with the source version where relevant.
- **Change:** the statement, proof, or definition being added or fixed.
- **Dependencies:** any changed public declarations and affected downstream uses.
- **Proof status:** remaining `sorry` placeholders, including known gaps in
  dependencies used by the contribution.
- **Checks:** the build commands run and their results.
- **Credits:** the people responsible for mathematical review, statements, proofs, and library integration, as applicable.

For documentation-only changes, source references and Lean builds are needed only where relevant to the change.

## Contributors

### Main Contributors

- Zichen Wang, School of Mathematical Sciences, Peking University, CHINA (princhernwang@gmail.com)
- Bohan Fang, Beijing International Center for Mathematical Research, Peking University, CHINA (b-fang@bicmr.pku.edu.cn)
- Qizheng Yin, Beijing International Center for Mathematical Research, Peking University, CHINA (yinqizheng@math.pku.edu.cn)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)

### Formalization

- Chenyi Li, Wanli Ma, Ziyu Wang

### Mathematics

- Jiedong Jiang, Haoda Li

See [ATTRIBUTION.md](ATTRIBUTION.md) for the current team credits and how individual contributions are recorded.


## Publications

### Autoformalization and Automatic Theorem Proving

- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen, M2F: Automated Formalization of Mathematical Literature at Scale
- Wanli Ma, Zichen Wang, Ziyu Wang, Zaiwen Wen, LIFT: Library Integration of Formalized Theorems for Reusable Mathematical Knowledge
- Zichen Wang, Yiming Fu, Ziyu Wang, Kun Yuan, Zaiwen Wen, The Future Is the Test: Library Abstractions for Mathematics Not Yet Written


## Acknowledgments

The mathematical source is the [Stacks Project](https://stacks.math.columbia.edu/), by Johan de Jong and the Stacks Project contributors. We thank the Lean and Mathlib communities for the foundations and mathematical infrastructure used by this project.

## Copyright

Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.

Released under the [Apache License 2.0](LICENSE).
