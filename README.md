# Formalizing the Stacks Project in Lean

We are building **ReasLib**, a shared Lean 4 library of mathematical definitions,
theorem statements, proofs, and dependencies, based on Mathlib and the
[Stacks Project](https://stacks.math.columbia.edu/). Our goal is to make this
mathematics reusable across chapters, papers, and future research projects.
AI-assisted formalization and library integration are organized through
[Quokka](https://quokka.reaslab.io).

We have completed an initial Lean formalization of the Stacks mathematical
statements and organized the results into ReasLib. **Many proofs remain unfinished
and are marked with `sorry`.** Statement formalization, proof completion, and
mathematical review are separate parts of the work.

## Why this library

- **Shared mathematical interfaces.** Reusable definitions and results live in
  subject-based modules. Several source entries can use the same declarations,
  with their maps and compatibility properties maintained together.
- **A clear link to the source.** Chapter-based files record how those declarations
  correspond to the original Stacks entries. Readers can follow the textbook,
  while library users work with the mathematical interfaces.
- **Reuse beyond Stacks.** ReasLib remains independent of the chapter files.
  Other papers and projects can import its modules directly, and new applications
  help identify and improve the interfaces they need.

## Library organization

| Path | Contents |
| --- | --- |
| [`ReasLib/`](ReasLib/) | Shared mathematical definitions, statements, and proofs, organized by subject. |
| [`stacks_project/`](stacks_project/) | Chapter-based checks linking shared declarations to the original Stacks entries. |
| [`lakefile.toml`](lakefile.toml) | Library targets and dependency revisions. |
| [`lean-toolchain`](lean-toolchain) | Lean version used by the project. |

The dependency direction is:

```text
Mathlib → ReasLib → Stacks chapter checks / other mathematical projects
```

The chapter files import shared modules and use `#check`, `recall`, and tag
annotations to record the correspondence with the source. Where present,
`@[stacks TAG]` identifies the original entry at
`https://stacks.math.columbia.edu/tag/TAG`. Mathematical review checks that the
definitions, assumptions, and conclusions express the intended source content.

### One interface, several source entries

The constant-sheaf interfaces are collected in
[`ReasLib.Topology.Sheaves.Types.Constant`](ReasLib/Topology/Sheaves/Types/Constant.lean).
They connect Mathlib's canonical constant sheaf to the concrete model of
locally constant functions and provide related stalk maps.

| Stacks entry | Use of the shared interface |
| --- | --- |
| [006W](https://stacks.math.columbia.edu/tag/006W) | Relates the constant sheaf to the source's locally constant function model. |
| [007B](https://stacks.math.columbia.edu/tag/007B) | Uses the constant-presheaf and constant-sheaf stalk interfaces. |
| [0081](https://stacks.math.columbia.edu/tag/0081) | Uses the comparison from sheafification to the concrete function model. |

These chapter entries share one module, so the maps and their properties have a
common place to be maintained. Some of those properties still have unfinished
proofs.

### An application beyond Stacks

In a separate application, we have used ReasLib to formalize the statements and
data interfaces needed for **Uniform Mordell–Lang for curves**, through
`JacobianFoundations` and an AnnalsChallenge adapter. The six audited application
entry points have no reachable non-`Prop` `sorry` holes; the main theorem and
other proposition-level obligations remain unproved. It also exposed a Picard/sheafification interface issue that
led to a shared-interface repair. This is how a new paper can both use and improve
the library.

The [independent UML application](applications/uniform-mordell-lang/) is included
with Lean 4.32.0 and the same Mathlib pin as the Stacks root project, a ReasLib
source snapshot, build instructions, and a data-hole audit. It retains separate
Lake projects and build targets.

#### ReasLib reuse

The two JacobianFoundations entry modules contain **6 direct ReasLib imports**.
The UML statement's deduplicated transitive import closure contains **968 ReasLib
modules**, within the bundled 1,002-module snapshot. These figures exclude
Mathlib modules.

| Application consumer | Direct ReasLib imports | Interfaces called in the consumer | Mathematical role |
|---|---:|---|---|
| [Genus.lean](applications/uniform-mordell-lang/jacobian-foundations/JacobianFoundations/Genus.lean) | 4 | `Scheme.Hom.cohomologyFinrank`; `SheafOfModules.LargeSite.injectiveResolutions` | Structure-sheaf cohomology and the scalar action used for genus. |
| [Picard.lean](applications/uniform-mordell-lang/jacobian-foundations/JacobianFoundations/Picard.lean) | 2 | `RelativePicard.component`; `RelativePicard.componentZeroGrpObj`; `RelativePicard.sectionClass`; `RelativePicard.degreeZeroGroupRepresentation` | Degree-zero Picard representation, Jacobian group structure, and the normalized graph class defining the pointed Abel–Jacobi map. |

Mathlib supplies the underlying objects and general mathematical APIs; ReasLib
organizes the shared cohomology and Picard interfaces; the application adapters
assemble these into the paper's statement. The 968-module count measures imports;
the table identifies concrete interface calls. The application README lists
[all six direct imports and the interface owners](applications/uniform-mordell-lang/#reaslib-reuse),
with a [source-based import manifest](applications/uniform-mordell-lang/validation/reaslib-reuse.json).

#### Required imports

The 968 modules form the current loaded import closure. To identify the parts
used by the statement, we also traced elaborated declaration types, data
definitions, and structure field specifications, excluding bodies of
`Prop`-valued declarations:

| Scope | ReasLib owner modules | Referenced ReasLib declarations |
|---|---:|---:|
| Final `UniformMordellLang.theorem_1_1` statement and its data definitions | **49** | **274** |
| All six application interfaces, including the pointed Abel–Jacobi map | **79** | **460** |

The [complete module lists and declaration witnesses](applications/uniform-mordell-lang/REASLIB_REQUIRED_MODULES.md)
identify these owners. Their source files still load their own module dependencies.
Inline proof references inside retained data definitions remain in this trace.

Compile experiments also identify this fine-grained entry profile for the
complete existing consumers:

| Consumer | Required ReasLib entry in the tested profile | Reason |
|---|---|---|
| Genus | `ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections` | Canonical cohomology with the scalar action and finrank. |
| Picard | `ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Pointed` | The graph-section class used by the Abel–Jacobi construction. |
| Picard | `ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Group` | Degree-zero representation and Jacobian group structure. |
| Picard compatibility helper | `ReasLib.AlgebraicGeometry.Hilbert.SmoothProperCurve` | Required by the retained `graphHilbertPoint` helper. |

Every entry in this profile is required when the other entries and declarations
are held fixed. A separate core-only probe omitting `graphHilbertPoint` compiles
with the first three entries. The complete profile still loads **960 modules**
through the existing library sources. See the [31 compile experiments and scope definitions](applications/uniform-mordell-lang/#required-imports)
for the distinction between required entry points, referenced declaration owners,
and the full source import closure. The published import lines remain unchanged.

#### Build and audit results

The [recorded validation](applications/uniform-mordell-lang/validation/validation.json)
passes all nine checks:

| Check | Result |
|---|---|
| Toolchain and Mathlib pins | Match the Stacks root project |
| Bundled ReasLib snapshot and JacobianFoundations | All 1,002 ReasLib modules build |
| UML application and representation guards | Build and interface checks pass |
| Transitive audit of six application entry points | Zero reachable non-`Prop` `sorry` holes |
| Audit regression fixtures | Direct and nested data holes and unknown roots are rejected; proof holes remain permitted |

The audit checks declaration types and values, including opaque proof bodies
and the arguments of proposition-valued holes. The application README gives
[statement correspondence and review scope](applications/uniform-mordell-lang/#statement-correspondence-and-review-scope).
These results cover the independent application snapshot; the full Stacks root
library was not rebuilt. Deferred propositions can still supply data through
existence statements, so the audit does not certify their mathematical truth.

## Library overview

ReasLib covers algebraic geometry, category theory, algebra, ring theory,
topology, and related subjects. The following repository statistics were
reported on **5 November 2026** and cover `ReasLib/`.

| Subject directory | Lean source files | Definitions | Theorem declarations | Source lines |
| --- | ---: | ---: | ---: | ---: |
| [AlgebraicGeometry](ReasLib/AlgebraicGeometry/) | 12,892 | 53,670 | 56,538 | 1,509,581 |
| [CategoryTheory](ReasLib/CategoryTheory/) | 5,293 | 16,479 | 28,484 | 600,724 |
| [Algebra](ReasLib/Algebra/) | 3,248 | 15,454 | 19,451 | 428,092 |
| [RingTheory](ReasLib/RingTheory/) | 2,895 | 6,964 | 13,084 | 287,777 |
| [Topology](ReasLib/Topology/) | 506 | 1,749 | 1,966 | 46,958 |
| [AlgebraicTopology](ReasLib/AlgebraicTopology/) | 369 | 1,570 | 2,814 | 49,527 |
| Other subject directories | 431 | 1,014 | 2,009 | 49,548 |
| **Total** | **25,634** | **96,900** | **124,346** | **2,972,207** |

Theorem declaration counts include statements whose proofs contain `sorry`;
they are not counts of completed proofs. The table does not include the
chapter-check files or Mathlib.

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
2. **Improve a shared interface.** Reuse existing Mathlib and ReasLib objects,
   connect equivalent representations, or make an interface useful to more
   downstream results.
3. **Adapt an existing proof or fill a genuine gap.** First look for suitable
   existing results. Align definitions and assumptions before transferring a
   proof, and preserve its source and contributor credits.
4. **Bring a new application.** Try using the library for a paper, textbook, or
   another mathematical domain. A small example showing a missing or awkward
   interface is a useful contribution.

### Preparing a pull request

1. Work on a focused change in your own branch or fork.
2. Put reusable mathematical content in `ReasLib/`. When changing a Stacks
   formalization, update its chapter correspondence too. ReasLib modules should
   remain independent of `stacks_project` chapter modules.
3. Open a [pull request](https://github.com/optpku/stacks/pulls) explaining the
   mathematical source, your change, and its effect on existing users.

Please include:

- **Source:** the Stacks tag or other reference, with its version where relevant.
- **Change:** the statement, proof, definition, or interface being added or fixed.
- **Dependencies:** changed public declarations and affected downstream uses.
- **Proof status:** remaining `sorry` placeholders, including known gaps in dependencies.
- **Credits:** the people responsible for statements, proofs, mathematical review,
  and library integration; retain existing author notices and identify AI assistance.

## Contributors

### Main Contributors

- Zichen Wang, School of Mathematical Sciences, Peking University, CHINA (princhernwang@gmail.com)
- Bohan Fang, Beijing International Center for Mathematical Research, Peking University, CHINA (b-fang@bicmr.pku.edu.cn)
- Qizheng Yin, Beijing International Center for Mathematical Research, Peking University, CHINA (yinqizheng@math.pku.edu.cn)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)

### Formalization

- Chenyi Li, Wanli Ma, Ziyu Wang

### Mathematics

- Jiedong Jiang
- Haoda Li
- Yuefeng Wang
- Yongle Hu
- Ziheng Zhang
- Ze Yuan
- Yiming Fu
- Yixiao Li
- Zhenhua Wu
- Nailin Guan
- Tian Zhou
- Yuze Sun

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
