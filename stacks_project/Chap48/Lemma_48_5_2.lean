module

public import ReasLib.CategoryTheory.Adjunction.BaseChange.HorizontalComposition
import StacksCheckRecall

open CategoryTheory
open scoped CategoryTheory.TwoSquare

universe uA uB uC uD uE uF vA vB vC vD vE vF

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
variable {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}

/- Lemma 48.5.2: For two horizontally composable cartesian base-change squares of
quasi-compact and quasi-separated schemes whose indicated morphisms are Tor independent, the
maps of 48.5.0.1 compose to the map for the outer rectangle. After identifying the outer dual
square with the horizontal composite of the two dual squares, this is compatibility of inverse
mates with horizontal composition and composite adjunctions. -/
@[stacks 0ATR] #check
  (CategoryTheory.DerivedBaseChange.mapOfRight_hcomp :
    ∀ (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
      (alpha : TwoSquare R₁ H G R₂) (beta : TwoSquare R₃ K H R₄),
      CategoryTheory.DerivedBaseChange.mapOfRight
          (adj₁.comp adj₃) (adj₂.comp adj₄) (beta ≫ₕ alpha) =
        CategoryTheory.DerivedBaseChange.mapOfRight adj₁ adj₂ alpha ≫ᵥ
          CategoryTheory.DerivedBaseChange.mapOfRight adj₃ adj₄ beta)
