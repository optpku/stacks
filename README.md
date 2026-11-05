# Formalizing the Stacks Project in Lean

We are formalizing the [Stacks Project](https://stacks.math.columbia.edu/) in
Lean 4, building on Mathlib, and organizing the resulting mathematical
definitions, statements, and proofs into **ReasLib**, a shared and reusable
library. The Stacks Project is a comprehensive open-source reference that
systematically organizes knowledge in algebraic geometry. We have completed an
initial large-scale formalization of its mathematical statements in Lean 4 and
integrated the results into ReasLib.

Beyond formalizing individual statements, we consolidate shared mathematical
definitions across chapters and organize dependencies between mathematical
concepts and results, making the library easier to maintain, extend, and reuse.

## Statement design and library integration

Choices of definitions and abstraction level shape how a theorem
can be stated, proved, and reused. Our statement design follows three principles:

- **Build on Mathlib.** Reuse existing definitions, instances, and theorems,
  and build a shared library for mathematics that is still missing.
- **Align representations.** Coordinate objects and assumptions across chapters
  and papers. Connect alternative representations through equivalences and
  compatibility results, while retaining the link to the original statements.
- **Review the mathematics.** Mathematical reviewers check representations,
  hypotheses, and conclusions against the source. AI-assisted generation and
  compilation feedback support this work throughout library integration.

Work proceeds through **Statement → Library Integration → Proof**: organize
definitions, statements, and pending proof obligations, and consolidate shared
statements.

## Library organization

| Path | Contents |
| --- | --- |
| [`ReasLib/`](ReasLib/) | Shared mathematical definitions, statements, and proofs, organized by subject. |
| [`stacks_project/`](stacks_project/) | Chapter-based checks linking shared declarations to the original Stacks entries. |

The dependency direction is:

```text
Mathlib → ReasLib → Stacks chapter checks / other mathematical projects
```

The chapter files import shared modules and use `#check`, `recall`, and tag
annotations to record the correspondence with the source. Where present,
`@[stacks TAG]` identifies the original entry at
`https://stacks.math.columbia.edu/tag/TAG`. Mathematical review checks that the
definitions, assumptions, and conclusions express the intended source content.

### An application beyond Stacks

Building on Imperial College London's
[AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge), the
[Uniform Mordell–Lang application](applications/uniform-mordell-lang/)
reuses ReasLib's cohomology and relative Picard declarations through
`JacobianFoundations` to construct genus, Jacobian, group structure, and
pointed Abel–Jacobi data. The theorem statement is formalized; mathematical
proofs remain deferred.

See the application for [reuse and dependency tables](applications/uniform-mordell-lang/#reaslib-reuse)
and [build and audit results](applications/uniform-mordell-lang/#build-and-validation).

## Library overview

ReasLib covers algebraic geometry, category theory, algebra, ring theory,
topology, and related subjects. These counts cover the top-level `ReasLib/`;
see the [source snapshot and counting method](docs/reaslib-statistics.json).

| Subject | Lean source files | Other declarations | Theorems / lemmas | Source lines |
| --- | ---: | ---: | ---: | ---: |
| [AlgebraicGeometry](ReasLib/AlgebraicGeometry/) | 12,893 | 53,669 | 56,538 | 1,509,871 |
| [CategoryTheory](ReasLib/CategoryTheory/) | 5,294 | 16,479 | 28,484 | 601,585 |
| [Algebra](ReasLib/Algebra/) | 3,249 | 15,451 | 19,451 | 428,521 |
| [RingTheory](ReasLib/RingTheory/) | 2,896 | 6,964 | 13,084 | 288,028 |
| [Topology](ReasLib/Topology/) | 507 | 1,749 | 1,966 | 47,099 |
| [AlgebraicTopology](ReasLib/AlgebraicTopology/) | 370 | 1,570 | 2,814 | 49,665 |
| Other subjects | 425 | 1,014 | 2,009 | 47,438 |
| **Total** | **25,634** | **96,896** | **124,346** | **2,972,207** |

Each subject includes its matching umbrella file (for example,
`ReasLib/Algebra.lean`). Source lines include comments and blank lines.
Declaration counts are static source counts, excluding examples and generated
declarations. “Other declarations” includes definitions, instances, and type
declarations. Theorem/lemma counts include unfinished `sorry` proofs.
Chapter checks, Mathlib, and bundled application snapshots are excluded.

## How to use

### Explore the source locally

```sh
git clone https://github.com/optpku/stacks.git
cd stacks
```

Start from a subject in `ReasLib/`, or follow a chapter entry in
`stacks_project/` to the shared declarations it uses.

### Use ReasLib as a project dependency

Use the Lean version in [`lean-toolchain`](lean-toolchain) and a compatible
Mathlib revision. Add the following to your project's `lakefile.toml`, replacing
`<commit-or-tag>` with the revision you want to use:

```toml
[[require]]
name = "stacks_project"
git = "https://github.com/optpku/stacks.git"
rev = "<commit-or-tag>"
```

The Lake package name is `stacks_project`; the shared mathematical modules use
the `ReasLib` prefix. Import the module needed by your application, for example:

```lean
import ReasLib.Topology.Sheaves.Types.Constant

#check TopCat.Sheaf.Constant.toDiscrete
#check TopCat.Sheaf.Constant.toStalk
```

## Contributing

You can contribute with your own local Lean and AI tools. Useful starting points
include:

1. **Review a statement.** Choose a Stacks tag and check its definitions,
   assumptions, and conclusion against the source. Propose a correction or a
   clearer mathematical expression.
2. **Improve a shared statement.** Reuse existing Mathlib and ReasLib objects,
   connect equivalent representations, or make an interface useful to more
   downstream results.
3. **Adapt an existing proof or fill a genuine gap.** First look for suitable
   existing results. Align definitions and assumptions before transferring a
   proof, and preserve its source and contributor credits.
4. **Bring a new application.** Try using the library for a paper, textbook, or
   another mathematical domain. A small example showing a missing or awkward
   interface is a useful contribution.

## Related projects

[Quokka](https://quokka.reaslab.io/) coordinates AI-assisted formalization and
library integration using M2F.
[ReasBook](https://github.com/optpku/ReasBook), with its
[reading and review interface](https://reasbook.reaslab.io/), supports reading
formalized literature, exploring dependencies, and mathematical review.

Our longer-term goal is to connect ReasLib with
[ReasAtlas](https://atlas.reaslab.io/), a natural-language mathematical knowledge
graph, and extend this shared infrastructure to more mathematical fields.
We welcome mathematicians and research groups to help develop and review it.

## Contributors

### Main Contributors

- Zichen Wang, School of Mathematical Sciences, Peking University, CHINA (princhernwang@gmail.com)
- Bohan Fang, Beijing International Center for Mathematical Research, Peking University, CHINA (b-fang@bicmr.pku.edu.cn)
- Qizheng Yin, Beijing International Center for Mathematical Research, Peking University, CHINA (yinqizheng@math.pku.edu.cn)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)

### Formalization

- Chenyi Li, Wanli Ma, Ziyu Wang, Shu Miao, Min Cui

### Mathematics

Jiedong Jiang, Haoda Li, Yuefeng Wang, Yongle Hu, Ziheng Zhang, Ze Yuan, Yiming Fu, Yixiao Li, Zhenhua Wu, Nailin Guan, Tian Zhou, Yuze Sun.

See [ATTRIBUTION.md](ATTRIBUTION.md) for the current team credits and how individual contributions are recorded.


## Publications

### Autoformalization and Automatic Theorem Proving

- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen, M2F: Automated Formalization of Mathematical Literature at Scale
- Wanli Ma, Zichen Wang, Ziyu Wang, Zaiwen Wen, LIFT: Library Integration of Formalized Theorems for Reusable Mathematical Knowledge
- Zichen Wang, Yiming Fu, Ziyu Wang, Kun Yuan, Zaiwen Wen, The Future Is the Test: Library Abstractions for Mathematics Not Yet Written


## Acknowledgments

The mathematical source is the [Stacks Project](https://stacks.math.columbia.edu/), by Johan de Jong and the Stacks Project contributors. We thank the Lean and Mathlib communities for the foundations and mathematical infrastructure used by this project.

## Copyright

Copyright © 2026 Zichen Wang, Zaiwen Wen. All rights reserved.

Released under the [Apache License 2.0](LICENSE).
