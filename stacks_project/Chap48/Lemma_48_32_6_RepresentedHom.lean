module

public import ReasLib.CategoryTheory.Pro.RepresentedHom

@[expose] public section

open CategoryTheory

universe uA vA uB vB

/- Compatibility check of the promoted represented Hom bifunctor. -/
#check (CategoryTheory.Pro.representedHom :
  {A : Type uA} → [Category.{vA} A] → {B : Type uB} → [Category.{vB} B] →
    (A ⥤ Pro B) → Aᵒᵖ × B ⥤ Type vB)
