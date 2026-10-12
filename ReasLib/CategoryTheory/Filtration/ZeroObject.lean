/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

private noncomputable abbrev zeroObject : FilteredObject C where
  obj := (0 : C)
  filtration :=
    { toFun := fun _ ↦ ⊤
      monotone' := fun _ _ _ ↦ le_rfl }

private theorem isZero_zeroObject : IsZero (zeroObject : FilteredObject C) := sorry

noncomputable instance : HasZeroObject (FilteredObject C) :=
  ⟨⟨zeroObject, isZero_zeroObject⟩⟩

/-- Stacks 015S: the canonical zero filtered object has a finite filtration. -/
@[stacks 015S]
theorem isFinite_zero : (0 : FilteredObject C).IsFinite := sorry

/-- Stacks 015S: finite filtered objects contain a zero object, so their full subcategory has a
canonical zero object. -/
@[stacks 015S]
instance isFinite_containsZero :
    ObjectProperty.ContainsZero (FilteredObject.IsFinite : ObjectProperty (FilteredObject C)) where
  exists_zero := ⟨0, isZero_zero _, isFinite_zero⟩

end FilteredObject

end CategoryTheory
