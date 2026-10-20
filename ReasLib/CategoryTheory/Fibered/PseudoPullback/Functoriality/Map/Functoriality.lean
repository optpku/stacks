/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.ObjectComputations
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.MorphismComputations

/-!
# Functoriality of explicit pseudo-pullback maps

Identity and composition formulas for the map induced by a based cospan transformation.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂
universe uX₃ vX₃ uY₃ vY₃ uS₃ vS₃

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- The explicit pseudo-pullback map of the identity cospan transformation is the identity. -/
theorem map.id (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    map (BasedCospanTransform.id F G) =
      𝟙 (PseudoPullback F G) := sorry
/- Proof strategy: ext on the underlying functor and then use `hom_ext`; identity components act
trivially on both projections, and the three-step comparison pasting reduces to the stored one. -/

/-- Explicit pseudo-pullback maps respect composition of cospan transformations. -/
theorem map.comp
    {X₃ : BasedCategory.{vX₃, uX₃} C}
    {Y₃ : BasedCategory.{vY₃, uY₃} C}
    {S₃ : BasedCategory.{vS₃, uS₃} C}
    {F₃ : X₃ ⥤ᵇ S₃} {G₃ : Y₃ ⥤ᵇ S₃}
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂)
    (φ : BasedCospanTransform F₂ G₂ F₃ G₃) :
    map (ψ.comp φ) = map ψ ⋙ map φ := sorry
/- Proof strategy: ext on objects and morphisms through `hom_ext`. The left, right, and base
components reduce to functor composition; the only coherence is associativity of the three-step
comparison pasting in `mapObj`. -/

end
end PseudoPullback

end BasedCategory

end CategoryTheory
