/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Bifiltered.Category
public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms

@[expose] public section

/-!
# Zero morphisms of bifiltered objects

When the ambient category has zero morphisms, bifiltered objects inherit zero morphisms and all
three forgetful functors preserve them.
-/

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.BifilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The zero underlying morphism preserves the first filtration. -/
theorem zero_preservesFirst (X Y : BifilteredObject C) (i : ℤ) :
    (Y.firstFiltration.stage i).Factors
      ((X.firstFiltration.stage i).arrow ≫ (0 : X.obj ⟶ Y.obj)) := sorry

/-- The zero underlying morphism preserves the second filtration. -/
theorem zero_preservesSecond (X Y : BifilteredObject C) (i : ℤ) :
    (Y.secondFiltration.stage i).Factors
      ((X.secondFiltration.stage i).arrow ≫ (0 : X.obj ⟶ Y.obj)) := sorry

/-- The zero morphism between bifiltered objects. -/
instance {X Y : BifilteredObject C} : Zero (X ⟶ Y) where
  zero :=
    { hom := 0
      preservesFirst := zero_preservesFirst X Y
      preservesSecond := zero_preservesSecond X Y }

/-- The underlying morphism of a zero bifiltered morphism is zero. -/
@[simp]
theorem zero_hom {X Y : BifilteredObject C} : (0 : X ⟶ Y).hom = 0 := sorry

/-- Bifiltered objects inherit zero morphisms from the ambient category. -/
instance : HasZeroMorphisms (BifilteredObject C) where
  zero X Y := inferInstance
  comp_zero := sorry
  zero_comp := sorry

/-- Forgetting to the first filtration preserves zero morphisms. -/
instance first_preservesZeroMorphisms :
    (first (C := C)).PreservesZeroMorphisms where
  map_zero := sorry

/-- Forgetting to the second filtration preserves zero morphisms. -/
instance second_preservesZeroMorphisms :
    (second (C := C)).PreservesZeroMorphisms where
  map_zero := sorry

/-- Forgetting both filtrations preserves zero morphisms. -/
instance forget_preservesZeroMorphisms :
    (forget (C := C)).PreservesZeroMorphisms where
  map_zero := sorry

/-- Exchanging the two filtrations preserves zero morphisms. -/
instance swap_preservesZeroMorphisms :
    (swap (C := C)).PreservesZeroMorphisms where
  map_zero := sorry

#synth HasZeroMorphisms (BifilteredObject C)
#synth (first (C := C)).PreservesZeroMorphisms
#synth (second (C := C)).PreservesZeroMorphisms
#synth (forget (C := C)).PreservesZeroMorphisms
#synth (swap (C := C)).PreservesZeroMorphisms

end CategoryTheory.BifilteredObject
