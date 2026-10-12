/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_34_4_Comparison

/-!
# Lemma 87.34.7

The affine étale site of the reduction of a formal algebraic space is
equivalent to the category of morphisms of formal algebraic spaces whose
domain is affine and which are representable by algebraic spaces and étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}
variable (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [Reduction X]

/-- Lemma 87.34.7: for a scheme `S` and a formal algebraic space `X` over `S`,
the category `X_affine,étale` is equivalent to the category of morphisms
`φ : U ⟶ X` of formal algebraic spaces such that `U` is an affine formal
algebraic space and `φ` is representable by algebraic spaces and étale. -/
@[stacks 0DEH]
def affineEtaleEquiv :
    AffineEtaleOver X ≌ AlgebraicSpace.affineEtaleSite (reduction X) :=
  CategoryTheory.Equivalence.mk toAffineEtale ofAffineEtale affineEtaleUnitIso
    affineEtaleCounitIso

/-- The forward functor of the identification in Lemma 87.34.7 sends
`φ : U ⟶ X` to a representing affine scheme of the fibre product
`U ×_X X_red`. -/
@[simp]
theorem affineEtaleEquiv_functor :
    (affineEtaleEquiv X).functor = toAffineEtale :=
  rfl

/-- The inverse functor of the identification in Lemma 87.34.7 sends an affine
scheme étale over `X_red` to the extension `U_{V,ψ}`. -/
@[simp]
theorem affineEtaleEquiv_inverse :
    (affineEtaleEquiv X).inverse = ofAffineEtale :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace
