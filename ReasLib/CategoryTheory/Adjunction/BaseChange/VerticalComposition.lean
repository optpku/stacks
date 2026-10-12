/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.BaseChange

open scoped CategoryTheory.TwoSquare

namespace CategoryTheory.DerivedBaseChange

universe uA uB uC uD uE uF vA vB vC vD vE vF

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
variable {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₃ : E ⥤ F} {R₃ : F ⥤ E}

/-- Taking the inverse mate sends vertical composition of right-adjoint squares to horizontal
composition of the corresponding left-adjoint squares. -/
public theorem mapOfRight_vcomp (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (alpha : TwoSquare R₁ H₁ G₁ R₂) (beta : TwoSquare R₂ H₂ G₂ R₃) :
    mapOfRight adj₁ adj₃ (alpha ≫ᵥ beta) =
      mapOfRight adj₁ adj₂ alpha ≫ₕ mapOfRight adj₂ adj₃ beta := sorry

end CategoryTheory.DerivedBaseChange
