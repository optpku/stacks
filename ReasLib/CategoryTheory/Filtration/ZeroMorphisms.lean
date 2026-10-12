/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Category

/-!
# Zero Morphisms on Filtered Objects

When the ambient category has zero morphisms, the category of filtered objects inherits them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace FilteredObject

/-- The zero morphism preserves every filtration stage. -/
theorem zero_preserves (X Y : FilteredObject C) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (0 : X.obj ⟶ Y.obj)) := by
  simpa using
    (Subobject.factors_zero : (Y.filtration.stage i).Factors
      (0 : (X.filtration.stage i : C) ⟶ Y.obj))

instance {X Y : FilteredObject C} : Zero (X ⟶ Y) where
  zero :=
    { hom := 0
      preserves := zero_preserves X Y }

@[simp] theorem zero_hom {X Y : FilteredObject C} : (0 : X ⟶ Y).hom = 0 := rfl

/- The preadditive instance supplies the canonical zero morphisms whenever available.  Keeping
   this fallback at the same low priority prevents a second zero-morphism choice from winning
   over `Preadditive.preadditiveHasZeroMorphisms` in filtered homological complexes. -/
instance (priority := 100) : HasZeroMorphisms (FilteredObject C) where
  zero X Y := inferInstance
  comp_zero {X Y} f Z := by
    exact FilteredObject.forget.map_injective <| by
      change f.hom ≫ 0 = 0; simp
  zero_comp X {Y Z} f := by
    exact FilteredObject.forget.map_injective <| by
      change (0 : X.obj ⟶ Y.obj) ≫ f.hom = 0; simp

namespace Hom

variable {X Y Z : FilteredObject C}

/-- A zero composite of filtered morphisms remains zero after forgetting the filtrations. -/
theorem hom_comp_eq_zero (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : f ≫ g = 0) :
    f.hom ≫ g.hom = 0 := sorry

end Hom

end FilteredObject

end CategoryTheory
