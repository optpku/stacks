module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoretic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pairings
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Lambda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Geometric characterizations of set-theoretic pre-equivalence relations

For a pre-relation on an algebraic space, set-theoretic pre-equivalence is characterized by
the images of the diagonal, flip, and transitivity pairings, and by equivalence relations on
algebraically closed field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open scoped Cardinal

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- A pre-relation is set-theoretically pre-equivalent exactly when its image contains the
images of the diagonal, flip, and transitivity pairings. -/
theorem isSetTheoreticPreEquivalence_iff_containsListImages (P : PreRelation U) :
    P.IsSetTheoreticPreEquivalence ↔
      Set.range (Points.map (diagonalPairing U).left) ⊆ Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map (P.flipHom).left) ⊆ Set.range (Points.map P.hom.left) ∧
        Set.range (Points.map (P.compPair).left) ⊆ Set.range (Points.map P.hom.left) :=
  sorry

/-- A pre-relation is set-theoretically pre-equivalent exactly when its point relation is an
equivalence relation over every sufficiently large algebraically closed field. -/
theorem isSetTheoreticPreEquivalence_iff_equivOnLargeFieldPoints (P : PreRelation U) :
    P.IsSetTheoreticPreEquivalence ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B),
        lambda P.left.left < #k → Equivalence (P.pointRel (Over.mk τ)) :=
  sorry

/-- If both projections are locally of finite type, a pre-relation is set-theoretically
pre-equivalent exactly when its point relation is an equivalence relation over every
algebraically closed field. -/
theorem isSetTheoreticPreEquivalence_iff_equivOnFieldPoints (P : PreRelation U)
    [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left] :
    P.IsSetTheoreticPreEquivalence ↔
      ∀ {k : Type u} [Field k] [IsAlgClosed k] {σ : Spec (.of k) ⟶ S}
        (τ : ofOver (Over.mk σ) ⟶ B), Equivalence (P.pointRel (Over.mk τ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
