module

public import stacks_project.Chap78.Lemma_78_22_2_Square

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace
open scoped Bicategory

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 78.22.2: Assume `B → S`, `(U, R, s, t, c)`, and `π : 𝒮_U ⟶ [U/R]` are as in
Lemma 78.20.2. The 2-commutative square of Lemma 78.20.3 with apex `𝒮_R`, legs `s` and `t`,
and comparison `α : π ∘ s ⟶ π ∘ t` is a 2-fibre product of stacks in groupoids on
`(Sch/S)_fppf`. -/
@[stacks 04M9, instance]
instance sourceTargetCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
