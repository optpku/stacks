# Stacks Project in Lean

English | [简体中文](README.zh-CN.md)

We formalize mathematics from the [Stacks Project](https://stacks.math.columbia.edu/)
into a **reusable Lean 4 library**. Building on Mathlib, we extract shared
mathematical definitions, constructions, and lemmas into `ReasLib`, while keeping
chapter-specific statements and their source references in `stacks_project`.

The core of this work is library organization: results that share mathematical
infrastructure can use a common declaration, and further formalizations can import the
relevant modules instead of rebuilding that infrastructure for each theorem.
The library is under development, with proofs and mathematical interfaces still
being completed and reviewed.

## A reusable mathematical library

We organize the formalization around three connected parts:

- **Shared infrastructure.** `ReasLib` groups definitions, constructions, and
  supporting lemmas by mathematical subject, including algebra, category theory,
  topology, and algebraic geometry.
- **Module interfaces.** Related concepts and results are organized into Lean
  namespaces and importable modules. This provides a common foundation for
  chapter results and for further library development.
- **Source correspondence.** `stacks_project` preserves chapter organization and
  Stacks tags where available, so readers can compare formal declarations with
  their mathematical sources.

For example, reusable infrastructure for ringed sites and topoi lives in
[`ReasLib/AlgebraicGeometry/RingedSite/`](ReasLib/AlgebraicGeometry/RingedSite/),
while chapter results live under [`stacks_project/`](stacks_project/).
An attribute such as `@[stacks 0DPK]` links a declaration to
[Stacks Project, Tag 0DPK](https://stacks.math.columbia.edu/tag/0DPK).

## Repository structure

| Path | Purpose |
| --- | --- |
| [`ReasLib/`](ReasLib/) | Reusable mathematical definitions, constructions, and lemmas |
| [`ReasLib.lean`](ReasLib.lean) | Library entry point |
| [`stacks_project/`](stacks_project/) | Chapter-organized formalizations and source correspondence |
| [`lean-toolchain`](lean-toolchain) | Lean version used by the project |
| [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json) | Library targets and dependencies |

The project uses **Lean 4.32.0** and mathlib. Use the checked-in toolchain and
Lake configuration when working with the library. See the
[Lean installation guide](https://leanprover-community.github.io/get_started.html)
and [contributor setup](CONTRIBUTING.md#contributor-setup-and-validation) to get started.

## Project status

The project organizes mathematics from the Stacks Project into chapter-based Lean
formalizations and the reusable library `ReasLib`, including material from
chapters 1–26 and later chapters. Work continues on completing proofs, improving
shared mathematical interfaces, and reviewing correspondence with the original text.

| Metric | Count |
| --- | --- |
| Distinct Stacks tags in chapter sources | 17,350 |
| Lean source files | 41,072 |
| Mathematical declarations (including definitions, structures, instances, and theorems) | 219,381 |
| Mathematical declarations in the shared library `ReasLib` | 144,213 |
| Proof entries | 122,179 |
| Proof entries without explicit placeholders | 9,351 |
| Unfinished proof entries with explicit placeholders | 112,828 |

Proof entries count `theorem`, `lemma`, and `example` commands. Absence of explicit
`sorry` or `admit` does not establish verification of a proof and its dependencies.

### Chapter coverage

| Chapters | Lean files | Distinct Stacks tags |
| --- | --- | --- |
| 1–26 | 6,178 | 5,824 |
| 27–34 | 1,800 | 1,761 |
| 35–111 | 14,441 | 9,766 |

Chapter counts cover sources in chapter directories and exclude the shared library.
A tag may occur in multiple chapters. See the [chapter-by-chapter table](docs/chapter-statistics.tsv)
and [statistics notes](docs/formalization-statistics.json) for details.

## Formalization authors

- **Statement formalization:** ReasBook team
- **Proof formalization:** ReasBook team

Author credits are recorded in code headers and updated as contributions are made.
See [ATTRIBUTION.md](ATTRIBUTION.md) for source attribution and license details.

## Contributions

**Everyone is welcome to submit Lean proofs through GitHub Pull Requests.**
A contribution can complete a single lemma, prove a shared supporting result,
improve a library interface, or correct a statement's correspondence with its
source. Small, focused contributions are valuable.

The library contains unfinished proofs marked with `sorry`. You can browse
[`ReasLib/`](ReasLib/) and [`stacks_project/`](stacks_project/), or use
[the proof inventory](docs/proof-debt.tsv) to find a starting point. The inventory
records explicit placeholders; absence of a placeholder does not certify a
result or its dependencies.

1. Choose a declaration and read the corresponding mathematical source.
2. Create a branch in your fork and complete the proof or improve the module.
3. Preserve source tags and the intended mathematical statement; put shared
   supporting lemmas in the reusable library.
4. Open a **Pull Request** with the file, declaration name, source tag or section,
   a brief explanation, and your validation result.

See [CONTRIBUTING.md](CONTRIBUTING.md) for details. For substantial work, open an
issue to coordinate with other contributors. Mathematical correspondence and
proof dependencies are part of review; adding an axiom or weakening a statement
is not a substitute for a proof.

## License and acknowledgments

Project code is released under [Apache-2.0](LICENSE). Third-party materials retain
their existing licenses; the original Stacks Project text retains its GNU Free
Documentation License. See [ATTRIBUTION.md](ATTRIBUTION.md).

We thank the Stacks Project authors and contributors, the Lean and mathlib
communities, and everyone contributing to this formalization. This is an
independent formalization effort.
