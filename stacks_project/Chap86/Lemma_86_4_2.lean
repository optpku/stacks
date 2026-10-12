/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.BaseChange.VerticalComposition
import StacksCheckRecall

open CategoryTheory
open scoped CategoryTheory.TwoSquare

universe uA uB uC uD uE uF vA vB vC vD vE vF

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
variable {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₃ : E ⥤ F} {R₃ : F ⥤ E}

/- Lemma 86.4.2: For two vertically stacked cartesian squares of qcqs algebraic spaces over a
scheme S, with (f, l) and (g, m) Tor independent, the maps of 86.4.1.1 compose to the map for the
outer rectangle. After identifying the outer dual square with the vertical composite of the two
dual squares, this is compatibility of inverse mates with composition. -/
@[stacks 0E5E] #check
  (CategoryTheory.DerivedBaseChange.mapOfRight_vcomp :
    (adj₁ : L₁ ⊣ R₁) → (adj₂ : L₂ ⊣ R₂) → (adj₃ : L₃ ⊣ R₃) →
      (alpha : TwoSquare R₁ H₁ G₁ R₂) → (beta : TwoSquare R₂ H₂ G₂ R₃) →
        CategoryTheory.DerivedBaseChange.mapOfRight adj₁ adj₃ (alpha ≫ᵥ beta) =
          CategoryTheory.DerivedBaseChange.mapOfRight adj₁ adj₂ alpha ≫ₕ
            CategoryTheory.DerivedBaseChange.mapOfRight adj₂ adj₃ beta)
