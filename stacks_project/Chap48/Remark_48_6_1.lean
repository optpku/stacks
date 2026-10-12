/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.BaseChange.HorizontalComposition
public import ReasLib.CategoryTheory.CommSq.Iso
import StacksCheckRecall

open CategoryTheory
open scoped CategoryTheory.TwoSquare

universe u v uA uB uC uD uE uF vA vB vC vD vE vF

variable {𝒞 : Type u} [Category.{v} 𝒞]
variable {restrictedSource restrictedTarget localSource localTarget : 𝒞}
variable (restrictedGlobal : restrictedSource ⟶ restrictedTarget)
  (localBaseChange : localSource ⟶ localTarget)
  (sourceComparison : restrictedSource ⟶ localSource)
  (targetComparison : restrictedTarget ⟶ localTarget)
variable [IsIso sourceComparison] [IsIso targetComparison]
variable (comparisonSq :
  CommSq restrictedGlobal sourceComparison targetComparison localBaseChange)

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]
variable {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}

/- Remark 48.6.1: Consider a Tor-independent cartesian square of quasi-compact and
quasi-separated schemes with vertical maps `f' : X' ⟶ Y'` and `f : X ⟶ Y` and horizontal
maps `g' : X' ⟶ X` and `g : Y' ⟶ Y`. For affine opens `V ⊆ Y` and `V' ⊆ Y'` satisfying
`g(V') ⊆ V`, let `U` and `U'` be the corresponding pullbacks in `X` and `X'`. If the
open-restriction comparisons 48.4.1.1 for `K` over `U ⟶ V` and for `Lg^*K` over `U' ⟶ V'`
are isomorphisms, horizontal composition identifies the restriction to `U'` of the global
base-change map `L(g')^*a(K) ⟶ a'(Lg^*K)` with the base-change map for the cartesian square
from `U' ⟶ U` to `V' ⟶ V`. Thus `IsIso` cancellation reduces checking invertibility of the
restricted global map to checking the base-change map for this last square. This is the
horizontal-composition formula of Lemma 48.5.2, since 48.4.1.1 is itself a base-change map. -/
@[stacks 0E9S] #check
  (CategoryTheory.CommSq.Iso.isIso_top_iff_bottom restrictedGlobal localBaseChange
      sourceComparison targetComparison comparisonSq :
    IsIso restrictedGlobal ↔ IsIso localBaseChange)

#check
  (CategoryTheory.CommSq.Iso.arrowIso restrictedGlobal localBaseChange
      sourceComparison targetComparison comparisonSq :
    Arrow.mk restrictedGlobal ≅ Arrow.mk localBaseChange)

#check
  (CategoryTheory.DerivedBaseChange.mapOfRight_hcomp :
    ∀ (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
      (alpha : TwoSquare R₁ H G R₂) (beta : TwoSquare R₃ K H R₄),
      CategoryTheory.DerivedBaseChange.mapOfRight
          (adj₁.comp adj₃) (adj₂.comp adj₄) (beta ≫ₕ alpha) =
        CategoryTheory.DerivedBaseChange.mapOfRight adj₁ adj₂ alpha ≫ᵥ
          CategoryTheory.DerivedBaseChange.mapOfRight adj₃ adj₄ beta)
