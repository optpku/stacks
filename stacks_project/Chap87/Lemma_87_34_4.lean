/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_34_4_Comparison

/-!
# Lemma 87.34.4

The affine étale site of the reduction of an affine formal algebraic space is
equivalent to the category of morphisms of affine formal algebraic spaces that
are representable by algebraic spaces and étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}
variable (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [Reduction X]

/-- Lemma 87.34.4: Let `S` be a scheme. Let `X` be an affine formal algebraic
space over `S`. Then `X_affine,étale` is equivalent to the category whose
objects are morphisms `φ : U ⟶ X` of formal algebraic spaces such that `U` is
an affine formal algebraic space and `φ` is representable by algebraic spaces
and étale. -/
@[stacks 0DEE]
def affineEtaleOverEquiv
    (hX :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X) :
    AffineEtaleOver X ≌ AlgebraicSpace.affineEtaleSite (reduction X) :=
  let _ := hX
  CategoryTheory.Equivalence.mk toAffineEtale ofAffineEtale affineEtaleUnitIso
    affineEtaleCounitIso

/-- The forward functor of the identification in Lemma 87.34.4 sends
`φ : U ⟶ X` to a representing affine scheme of the fibre product
`U ×_X X_red`. -/
@[simp]
theorem affineEtaleOverEquiv_functor
    (hX :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X) :
    (affineEtaleOverEquiv X hX).functor = toAffineEtale :=
  rfl

/-- The inverse functor of the identification in Lemma 87.34.4 sends an affine
scheme étale over `X_red` to the extension `U_{V,ψ}`. -/
@[simp]
theorem affineEtaleOverEquiv_inverse
    (hX :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X) :
    (affineEtaleOverEquiv X hX).inverse = ofAffineEtale :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace
