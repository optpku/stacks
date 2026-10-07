module

public import Mathlib.RingTheory.Algebraic.Defs
public import stacks_project.Chap65.Example_65_14_7_ArtinSchreier
public import stacks_project.Chap65.Example_65_14_7_Space
public import stacks_project.Chap65.Lemma_65_14_6_Equivariant
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
open AlgebraicGeometry.Scheme.PreRelation

/- Example 65.14.7 (1): with `S = Spec ℚ`, `U = Spec algebraicQ` and
`G = Gal(algebraicQ / ℚ)` acting in the obvious way on `U`, property `(*)` of
Lemma 65.14.3 holds, so the coproduct relation is an étale equivalence relation. -/
@[stacks 02Z6]
#check instIsResidueFieldFree_action
@[stacks 02Z6]
#check (instIsEtaleEquivalenceRelation_ofAut action)

/- Example 65.14.7 (2): the quotient `X = Spec algebraicQ / G` is an algebraic space
over `S = Spec ℚ`. -/
@[stacks 02Z6]
#check sheafOfPoints
@[stacks 02Z6]
#check sheafOfPoints_spec

/- Example 65.14.7 (3): by the Artin–Schreier theorem the only finite subgroups of
`Gal(algebraicQ / ℚ)` are `{1}` and the conjugates of the order-two group generated
by complex conjugation, equivalently `Gal(algebraicQ / realIntersection)`. -/
@[stacks 02Z6]
#check finite_subgroup_eq_bot_or_isConj

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- Example 65.14.7 (4): if `Spec k ⟶ X` is a morphism with `k` algebraic over `ℚ`,
then `k` is `ℚ`-algebra isomorphic to `algebraicQ` or to `realIntersection`. -/
@[stacks 02Z6]
theorem eq_algebraicQ_or_realIntersection {k : Type} [Field k] [Algebra ℚ k]
    [Algebra.IsAlgebraic ℚ k] (f : specToQuotientHom action (FieldExtension.specMap ℚ k)) :
    Nonempty (k ≃ₐ[ℚ] algebraicQ) ∨ Nonempty (k ≃ₐ[ℚ] realIntersection) := sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
