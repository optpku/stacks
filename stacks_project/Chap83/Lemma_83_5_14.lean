module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Geometric
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open scoped Cardinal

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/- Lemma 83.5.14: a pre-relation is set-theoretically pre-equivalent exactly when its image
contains the diagonal, flip, and transitivity pairing images. -/
@[stacks 0491] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticPreEquivalence_iff_containsListImages :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U),
      P.IsSetTheoreticPreEquivalence ↔
        Set.range (Points.map (diagonalPairing U).left) ⊆ Set.range (Points.map P.hom.left) ∧
          Set.range (Points.map P.flipHom.left) ⊆ Set.range (Points.map P.hom.left) ∧
          Set.range (Points.map P.compPair.left) ⊆ Set.range (Points.map P.hom.left))

#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticPreEquivalence_iff_equivOnLargeFieldPoints :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U),
      P.IsSetTheoreticPreEquivalence ↔
        ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
          (τ : ofOver (Over.mk σ) ⟶ B),
          lambda P.left.left < #k → Equivalence (P.pointRel (Over.mk τ)))

#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticPreEquivalence_iff_equivOnFieldPoints :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
      [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left],
      P.IsSetTheoreticPreEquivalence ↔
        ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
          (τ : ofOver (Over.mk σ) ⟶ B), Equivalence (P.pointRel (Over.mk τ)))

end AlgebraicGeometry.AlgebraicSpace.PreRelation
