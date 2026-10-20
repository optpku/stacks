/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms

/-!
# Zero Object in Filtered Objects

When the ambient category has a zero object, the category of filtered objects inherits one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

namespace FilteredObject

/-- The filtered object whose ambient object is zero and every stage is maximal. -/
noncomputable abbrev zeroObject : FilteredObject C where
  obj := (0 : C)
  filtration :=
    { toFun := fun _ ↦ ⊤
      monotone' := fun _ _ _ ↦ le_rfl }

/-- The canonical zero filtered object is a zero object. -/
theorem isZero_zeroObject : IsZero (zeroObject : FilteredObject C) := sorry

/-- The zero object structure on filtered objects is induced by the ambient zero object. -/
@[reducible] noncomputable def hasZeroObject : HasZeroObject (FilteredObject C) :=
  ⟨⟨zeroObject, isZero_zeroObject⟩⟩

/-- The canonical zero-object instance on filtered objects. -/
noncomputable instance instHasZeroObject : HasZeroObject (FilteredObject C) := hasZeroObject

/-- The canonical zero filtered object has a finite filtration. -/
@[stacks 015S]
theorem isFinite_zero : (0 : FilteredObject C).IsFinite := sorry

/-- Finite filtered objects contain a zero object, so their full subcategory has a canonical zero
object. -/
@[stacks 015S]
instance isFinite_containsZero :
    ObjectProperty.ContainsZero (FilteredObject.IsFinite : ObjectProperty (FilteredObject C)) where
  exists_zero := ⟨0, isZero_zero _, isFinite_zero⟩

end FilteredObject

end CategoryTheory
