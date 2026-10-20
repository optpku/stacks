module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSpace
public import stacks_project.Chap83.Definition_83_4_1_Invariant

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/- Lemma 83.5.19: let `B ⟶ S` as in Section 83.2, and let `j : R ⟶ U ×_B U` be a
set-theoretic pre-equivalence relation. A morphism `φ : U ⟶ X` is an orbit space for
`R` if and only if `φ` is `R`-invariant (`P.t ≫ φ = P.s ≫ φ`), the induced morphism
`(t, s) : R ⟶ U ×_X U` given by `P.induced hφ : P.left ⟶ pullback φ φ` is surjective,
and `φ` is surjective. This characterization applies for example if `j` is a
pre-equivalence relation, or comes from a groupoid in algebraic spaces over `B`, or
comes from the action of a group algebraic space over `B` on `U`. -/
@[stacks 049Z] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isOrbitSpace_iff_of_isSetTheoreticPreEquivalence :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
      (P : PreRelation U) (φ : U ⟶ X) (hP : P.IsSetTheoreticPreEquivalence),
    P.IsOrbitSpace φ ↔
      P.IsInvariant φ ∧ (∀ hφ : P.IsInvariant φ, Surjective (P.induced hφ).left) ∧
        Surjective φ.left)

end AlgebraicGeometry.AlgebraicSpace.PreRelation
