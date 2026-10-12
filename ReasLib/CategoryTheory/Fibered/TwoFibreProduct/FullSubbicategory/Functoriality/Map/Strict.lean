/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction

/-!
# Strict computations for full-subbicategory two-fibre-product maps

Identity and composition readouts for the selected componentwise map.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

/-- The map induced by the identity cospan transformation is the identity. -/
theorem map.id (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    map (CospanTransform.id F G) = 𝟙 (apex F G) := sorry

/-- Maps of explicit two-fibre products preserve composition of cospan transformations. -/
theorem map.comp
    {X₃ Y₃ S₃ : P.FullSubbicategory}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (psi : CospanTransform F₁ G₁ F₂ G₂)
    (phi : CospanTransform F₂ G₂ F₃ G₃) :
    map (psi.comp phi) = map psi ≫ map phi := sorry

end TwoFibreProduct

end CategoryTheory
