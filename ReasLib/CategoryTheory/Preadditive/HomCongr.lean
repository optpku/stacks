module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Preadditive.Basic

@[expose] public section

/-!
# Additive Hom Transport Along Isomorphisms

This module packages the ordinary `Iso.homCongr` equivalence as an additive equivalence in a
preadditive category. It is deliberately independent of derived categories and cochain
complexes, so it can be used whenever a calculation transports Hom groups across isomorphisms.
-/

namespace CategoryTheory

namespace Iso

universe v u

/-- Transporting morphisms along isomorphisms on source and target preserves addition. -/
theorem homCongr_add
    {C : Type u} [Category.{v} C] [Preadditive C] {X Y X₁ Y₁ : C}
    (eX : X ≅ X₁) (eY : Y ≅ Y₁) (f g : X ⟶ Y) :
    eX.homCongr eY (f + g) = eX.homCongr eY f + eX.homCongr eY g := sorry

/-- Isomorphisms on source and target induce an additive equivalence on the corresponding Hom
groups. -/
noncomputable def homCongrAddEquiv
    {C : Type u} [Category.{v} C] [Preadditive C] {X Y X₁ Y₁ : C}
    (eX : X ≅ X₁) (eY : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := eX.homCongr eY
    map_add' := homCongr_add eX eY }

end Iso

end CategoryTheory
