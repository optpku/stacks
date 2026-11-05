# Uniform Mordell Lang independent review

The target is Theorem 1.1 of Dimitrov, Gao, and Habegger, [Uniformity in Mordell–Lang for curves](https://annals.math.princeton.edu/2021/194-1/p04). For fixed `g ≥ 2` and `d ≥ 1`, a positive bound depending only on `g,d` controls the number of rational points on each smooth proper geometrically irreducible curve of genus `g` over a number field of degree at most `d`, in terms of its Jacobian's Mordell–Weil rank.

Review the mathematical representations, hypotheses, and quantified statements independently of the build results. Proofs remain deferred. A successful data-hole audit permits proposition-valued obligations and does not establish that those propositions are true.

Start with these source files:

| Source | Review focus |
|---|---|
| [Final statement](annals-uniform-mordell-lang/AnnalsChallenge/AnnalsOfMathematics/2021-194-1-UniformMordellLang.lean) | `IsUniformBound`, `exists_uniformBound`, `c`, and `theorem_1_1`; the order of quantifiers, positivity, point count, and rank. |
| [Challenge interface](annals-uniform-mordell-lang/AnnalsChallenge/Definitions/AlgebraicJacobian.lean) | Curve hypotheses, Jacobian properties, the pointed universal property, and Mordell–Weil propositions. |
| [Genus](jacobian-foundations/JacobianFoundations/Genus.lean) | `dim_k H¹(C,O_C)`, the structure-morphism scalar action, and the finite-dimensionality needed to interpret `finrank`. |
| [Picard construction](jacobian-foundations/JacobianFoundations/Picard.lean) | The representing object of the relative degree-zero Picard functor, its group structure, normalized graph class, and Abel–Jacobi map. |
| [ReasLib Picard interfaces](jacobian-foundations/ReasLib/AlgebraicGeometry/Scheme/Module/Picard/Relative/) | Presheaf and fppf sheafification models, degree components, tensor product, representability, and arbitrary-base pointed maps. |
| [Semantic checks](annals-uniform-mordell-lang/AnnalsChallenge/Tests/UniformMordellLangSemantics.lean) | Original challenge-facing types and quantifier structure. |
| [ReasLib checks](annals-uniform-mordell-lang/AnnalsChallenge/Tests/UniformMordellLangReasLib.lean) | Concrete carriers and normalization interfaces. |

Questions for mathematical review:

1. Do the curve hypotheses match the paper, including curves without a rational point? Are hypotheses needed for a particular geometric property kept separate from the general constructions?
2. Does genus use the actual structure-sheaf cohomology and the correct scalar action? Are the finite-dimensionality obligations correctly stated?
3. Does the chosen Jacobian represent the relative degree-zero Picard functor on all test schemes, including over fields where the curve has no point?
4. Are the line-bundle tensor product, duality, pullback, and fppf sheafification units concrete and mutually compatible? Are equivalent models related by canonical isomorphisms?
5. Are relative degree, subgroup closure, representability, and geometric-property obligations mathematically valid under their stated hypotheses?
6. Does the normalized graph construction represent `O(Δ − C × P)`, with the correct sign and product factor, so its pointed map sends `Q` to `O(Q−P)`?
7. Do the existence statements used to select data sufficiently constrain those data, without circularity?
8. Is the bound chosen before the field and curve, depending only on genus and field-degree bound? Does the small-model definition have an appropriate transport obligation for the universe-polymorphic final statement?
9. Do `ENat.card` and `freeRank` encode the intended cardinality and rank, with the required finiteness hypotheses?

See [source provenance](source-provenance.json) for the exact source snapshot and [validation results](validation/validation.json) for the independent builds and six-root audit. Reproduce them using the commands in [README.md](README.md).
