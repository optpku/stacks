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

From this directory, with Elan and Python 3 available:

```sh
(cd jacobian-foundations && lake exe cache get)
(cd annals-uniform-mordell-lang && lake exe cache get)
cd annals-uniform-mordell-lang
python3 scripts/check_uniform_mordell_lang.py
```

The checker builds **all bundled ReasLib modules and JacobianFoundations**, then builds the selected AnnalsChallenge application and checks. It reruns the data-hole audit for six roots and checks that non-`Prop` holes and unknown audit roots are rejected, while proposition-valued proof holes remain allowed. Generated artifacts and detailed logs stay in ignored `.lake` and `.work` directories.

These checks establish compilation and the stated syntactic audit properties for this independent application. The mathematical specifications and deferred propositions require review. They do not constitute a completed proof of Uniform Mordell–Lang or a build result for the full Stacks root library.

The challenge interfaces originate in [AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge/tree/e32eb1411db0d700ca874dd695aea92f78699db8). Original source copyright and author headers are retained, including Thomas Browning's UML statement and Christian Merten's AlgebraicJacobian interface. Both included projects retain their Apache 2.0 license files.
