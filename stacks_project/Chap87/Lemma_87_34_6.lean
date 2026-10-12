/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_34_6_Comparison
public import stacks_project.Chap87.Lemma_87_34_6_Over

/-!
# Lemma 87.34.6

The small étale site of algebraic spaces on the reduction of a formal
algebraic space is equivalent to the category of morphisms of formal
algebraic spaces that are representable by algebraic spaces and étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}
variable (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [Reduction X]

/-- Lemma 87.34.6: for a scheme `S` and a formal algebraic space `X` over `S`,
the category `X_spaces,étale` of algebraic spaces étale over the reduction of
`X` is equivalent to the category of morphisms `φ : U ⟶ X` of formal algebraic
spaces that are representable by algebraic spaces and étale. -/
@[stacks 0DEG]
def spacesEtaleEquiv :
    EtaleOver X ≌ AlgebraicSpace.spacesEtaleSite (reduction X) :=
  CategoryTheory.Equivalence.mk toSpacesEtale ofSpacesEtale unitIso counitIso

/-- The forward functor of the identification in Lemma 87.34.6 sends
`φ : U ⟶ X` to the fibre product `U ×_X X_red`. -/
@[simp]
theorem spacesEtaleEquiv_functor :
    (spacesEtaleEquiv X).functor = toSpacesEtale :=
  rfl

/-- The inverse functor of the identification in Lemma 87.34.6 sends
`ψ : V ⟶ X_red` to the functor of points `U_{V,ψ}`. -/
@[simp]
theorem spacesEtaleEquiv_inverse :
    (spacesEtaleEquiv X).inverse = ofSpacesEtale :=
  rfl

end AlgebraicGeometry.FormalAlgebraicSpace
