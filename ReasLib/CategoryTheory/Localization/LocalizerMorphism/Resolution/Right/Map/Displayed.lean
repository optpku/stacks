/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map
public import ReasLib.CategoryTheory.DisplayedCategory.Transport
import Mathlib.Tactic.CrossRefAttribute

/-!
# Displayed Category of Right Resolutions

Right resolutions vary over their resolved objects, while `RightResolution.Map f R S` is already
the dependent notion of morphism over a base arrow `f`.  This leaf packages that API as a
`DisplayedCategory`.  Its total category is consequently available from the generic displayed
category infrastructure, without introducing a second resolution-map owner.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.RightResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂}

namespace displayedCategory

/-- The displayed left-identity law for maps of right resolutions. -/
theorem id_comp {X Y : C₂} {f : X ⟶ Y}
    {R : Φ.RightResolution X} {S : Φ.RightResolution Y} (m : Map f R S) :
    (Category.id_comp f) ▸ Map.comp (Map.id R) m = m := sorry

/-- The displayed right-identity law for maps of right resolutions. -/
theorem comp_id {X Y : C₂} {f : X ⟶ Y}
    {R : Φ.RightResolution X} {S : Φ.RightResolution Y} (m : Map f R S) :
    (Category.comp_id f) ▸ Map.comp m (Map.id S) = m := sorry

/-- The displayed associativity law for maps of right resolutions. -/
theorem assoc {W X Y Z : C₂} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {R : Φ.RightResolution W} {S : Φ.RightResolution X}
    {T : Φ.RightResolution Y} {U : Φ.RightResolution Z}
    (m : Map f R S) (n : Map g S T) (q : Map h T U) :
    (Category.assoc f g h) ▸ Map.comp (Map.comp m n) q =
      Map.comp m (Map.comp n q) := sorry

end displayedCategory

/-- Right resolutions and their dependent maps, displayed over the target category. -/
@[stacks 0GSL "displayed category of right resolutions"]
def displayedCategory (Φ : LocalizerMorphism W₁ W₂) : DisplayedCategory C₂ where
  obj X := Φ.RightResolution X
  Hom f R S := Map f R S
  id R := Map.id R
  comp m n := Map.comp m n
  id_comp := displayedCategory.id_comp
  comp_id := displayedCategory.comp_id
  assoc := displayedCategory.assoc

namespace displayedCategory

/-- The displayed objects are right resolutions of the corresponding base object. -/
@[simp]
theorem obj (Φ : LocalizerMorphism W₁ W₂) (X : C₂) :
    (displayedCategory Φ).obj X = Φ.RightResolution X := sorry

/-- The displayed morphisms are maps of right resolutions over the corresponding base arrow. -/
@[simp]
theorem hom (Φ : LocalizerMorphism W₁ W₂) {X Y : C₂} (f : X ⟶ Y)
    (R : Φ.RightResolution X) (S : Φ.RightResolution Y) :
    (displayedCategory Φ).Hom f R S = Map f R S := sorry

/-- The displayed identity is the canonical identity map of a right resolution. -/
@[simp]
theorem id (Φ : LocalizerMorphism W₁ W₂) {X : C₂} (R : Φ.RightResolution X) :
    (displayedCategory Φ).id R = Map.id R := sorry

/-- Displayed composition is the canonical composition of right-resolution maps. -/
@[simp]
theorem comp (Φ : LocalizerMorphism W₁ W₂)
    {X Y Z : C₂} {f : X ⟶ Y} {g : Y ⟶ Z}
    {R : Φ.RightResolution X} {S : Φ.RightResolution Y} {T : Φ.RightResolution Z}
    (m : Map f R S) (n : Map g S T) :
    (displayedCategory Φ).comp m n = Map.comp m n := sorry

end displayedCategory

namespace Map

/-- Owner-level reindexing of a right-resolution map agrees with generic displayed transport. -/
@[simp, stacks 0GSL "displayed transport of right-resolution maps"]
theorem reindex_eq_cast {X Y : C₂} {f g : X ⟶ Y}
    {R : Φ.RightResolution X} {S : Φ.RightResolution Y}
    (h : f = g) (m : Map f R S) :
    reindex h m = DisplayedCategory.Hom.cast (displayedCategory Φ) h m := sorry

/-- Generic displayed transport can be converted back to right-resolution map reindexing. -/
@[stacks 0GSL "owner-level transport of right-resolution maps"]
theorem cast_eq_reindex {X Y : C₂} {f g : X ⟶ Y}
    {R : Φ.RightResolution X} {S : Φ.RightResolution Y}
    (h : f = g) (m : Map f R S) :
    DisplayedCategory.Hom.cast (displayedCategory Φ) h m = reindex h m := sorry

end Map

end CategoryTheory.LocalizerMorphism.RightResolution
