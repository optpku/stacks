# Uniform Mordell Lang statement application

This independent application formalizes the statement of Theorem 1.1 in Dimitrov, Gao, and Habegger, [Uniformity in Mordell–Lang for curves](https://annals.math.princeton.edu/2021/194-1/p04). Its genus, Jacobian, group structure, and pointed Abel–Jacobi map are built through JacobianFoundations and a bundled ReasLib source snapshot. Mathematical proofs remain deferred with `sorry`.

The application uses Lean **4.32.0** and Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. These pins match the Stacks root project. It retains its own Lake projects and is built separately from the root project. Its bundled `ReasLib` modules belong to this application workspace; they are not imported alongside the root project's ReasLib in a single Lean environment.

| Directory | Purpose |
|---|---|
| [annals-uniform-mordell-lang](annals-uniform-mordell-lang/) | The UML statement, challenge interfaces, semantic checks, and data-hole audit. Other AnnalsChallenge paper targets are omitted. |
| [jacobian-foundations](jacobian-foundations/) | Genus and Picard constructions, with the application-specific ReasLib snapshot. |
| [source-provenance.json](source-provenance.json) | Original repository commits, source hashes, and packaging adaptations. |
| [validation/validation.json](validation/validation.json) | Build and audit results for the published source files. |
| [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) | Mathematical review questions and source entry points. |

## ReasLib reuse

| Measure | Count | Scope |
|---|---:|---|
| Written direct ReasLib imports | **6** | Four in `JacobianFoundations.Genus`, two in `JacobianFoundations.Picard`. |
| Transitive ReasLib imports of the UML statement | **968** | Deduplicated source-module closure; excludes Mathlib and Lean. |
| Bundled ReasLib snapshot | **1,002** | The complete snapshot covered by the foundations build. |

The [import manifest](validation/reaslib-reuse.json) records the root module, all 968 ReasLib module names, and hashes of the application entry sources. Import counts describe module dependencies; the following interface table shows concrete calls in the application.

| Construction | Application definition | ReasLib interface called | Interface owner |
|---|---|---|---|
| Genus | `CurveJacobian.genus` | `Scheme.Hom.cohomologyFinrank` | [Cohomology/GlobalSections.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Cohomology/GlobalSections.lean) |
| Jacobian | `PicardConstruction.jacobian` | `RelativePicard.component C 0` | [Relative/Components.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Components.lean) |
| Group structure | `PicardConstruction.groupStructure` | `RelativePicard.componentZeroGrpObj` | [Relative/Group.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Group.lean) |
| Graph class and Abel–Jacobi map | `PicardConstruction.sectionGroupClass`, `normalizedClass`, `ofCurve` | `RelativePicard.sectionClass` and `RelativePicard.degreeZeroGroupRepresentation` | [Relative/Pointed.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Pointed.lean), [Relative/Group.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Group.lean) |

The `PicardConstruction` names are in `AlgebraicGeometry.CurveJacobian`. The current Abel–Jacobi construction uses the normalized graph class and its degree-zero group representation; `graphHilbertPoint` remains a separate compatibility helper.

All six directly imported modules are listed below. Paths are relative to `jacobian-foundations/ReasLib/`.

| Consumer | Directly imported module | Infrastructure made available |
|---|---|---|
| `Genus.lean` | [Algebra/Category/ModuleCat/Sheaf/GrothendieckLarge.lean](jacobian-foundations/ReasLib/Algebra/Category/ModuleCat/Sheaf/GrothendieckLarge.lean) | Large-site module-sheaf infrastructure and injective resolutions. |
| `Genus.lean` | [AlgebraicGeometry/RingedSpace/Module/Sections/Basic.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/RingedSpace/Module/Sections/Basic.lean) | Module-valued sections and restriction of scalars on a ringed space. |
| `Genus.lean` | [AlgebraicGeometry/Scheme/GlobalSections.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/GlobalSections.lean) | The global-functions ring and the map induced by the structure morphism. |
| `Genus.lean` | [AlgebraicGeometry/Scheme/Module/Cohomology/GlobalSections.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Cohomology/GlobalSections.lean) | Scheme-module cohomology with the induced scalar action and finrank. |
| `Picard.lean` | [AlgebraicGeometry/Scheme/Module/Picard/Relative/AbelMap.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/AbelMap.lean) | Relative Picard degree components, group interfaces, and Hilbert-divisor compatibility infrastructure. |
| `Picard.lean` | [AlgebraicGeometry/Scheme/Module/Picard/Relative/Pointed/Represented.lean](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/Pointed/Represented.lean) | Arbitrary-base pointed Picard interfaces, including the imported `sectionClass` construction. |

The shared layers follow `Mathlib → ReasLib → JacobianFoundations → AnnalsChallenge`. Mathlib provides standard carriers and general APIs, ReasLib provides the reusable geometry and cohomology interfaces, and the application defines the paper-specific bound and final statement. Import and interface counts do not measure completed proofs.

## Build and validation

From this directory, with Elan and Python 3 available:

```sh
(cd jacobian-foundations && lake exe cache get)
(cd annals-uniform-mordell-lang && lake exe cache get)
cd annals-uniform-mordell-lang
python3 scripts/check_uniform_mordell_lang.py
```

The checker builds **all 1,002 bundled ReasLib modules and JacobianFoundations**, then builds the selected AnnalsChallenge application and checks. It reruns the data-hole audit for six roots. Direct data holes, data holes nested in the arguments of a proposition-valued `sorryAx`, and unknown audit roots must be rejected; proposition-valued proof holes remain allowed. Generated artifacts and detailed logs stay in ignored `.lake` and `.work` directories.

The [recorded validation](validation/validation.json) passes all nine checks: toolchain, foundations build, application build, representation guards, six-root audit, and four audit regression fixtures. The audit traverses types and values of reachable declarations, including opaque proof bodies.

| Audited entry point | Reachable non-`Prop` `sorry` holes |
|---|---:|
| `AlgebraicGeometry.JacobianChallenge.genus` | 0 |
| `AlgebraicGeometry.JacobianChallenge.Jacobian` | 0 |
| `AlgebraicGeometry.JacobianChallenge.Jacobian.instGrpObj` | 0 |
| `AlgebraicGeometry.JacobianChallenge.Jacobian.ofCurve` | 0 |
| `UniformMordellLang.c` | 0 |
| `UniformMordellLang.theorem_1_1` | 0 |

## Statement correspondence and review scope

The interface checks preserve the shape of [Theorem 1.1](https://ziyangjeremygao.github.io/articles/UnifML.pdf): fix `g ≥ 2` and `d ≥ 1`, choose a positive `c(g,d)`, and then quantify over number fields of degree at most `d` and curves of genus `g`. The final statement uses `ENat.card` for the rational-point cardinality and the free rank of the Jacobian's rational-point group. No chosen rational point or algebraically closed ground field is required to construct the Jacobian; the pointed Abel–Jacobi map takes a point as an argument.

The paper uses projective curves, while the Lean interface uses proper, smooth, geometrically irreducible curves of relative dimension one. Proper curves over a field are projective; see [Stacks Lemma 33.43.4](https://stacks.math.columbia.edu/tag/0A26). The representation guards check the actual cohomology formula for genus, the degree-zero relative Picard functor, and the normalized graph class used by the Abel–Jacobi map.

These checks establish compilation, the checked interfaces, and the stated syntactic audit properties for this independent application. They cover the six entry points and their dependency graphs, rather than every declaration in the bundled snapshot. Admitted propositions can still be used to choose data. Finite-dimensionality and model comparisons for genus, Picard representability and geometric properties, Mordell–Weil, transport from small models, and the Uniform Mordell–Lang theorem remain mathematical proof obligations. The [independent review guide](INDEPENDENT_REVIEW.md) lists the corresponding source interfaces and questions. This is not a completed proof of Uniform Mordell–Lang or a build result for the full Stacks root library.

The challenge interfaces originate in [AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge/tree/e32eb1411db0d700ca874dd695aea92f78699db8). Original source copyright and author headers are retained, including Thomas Browning's UML statement and Christian Merten's AlgebraicJacobian interface. Both included projects retain their Apache 2.0 license files.
