module

public import ReasLib.CategoryTheory.Filtration.Indexed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered Objects

A filtered object in a category `C` is an object equipped with a decreasing `ℤ`-indexed filtration
by subobjects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A filtered object: an object of `C` equipped with a decreasing `ℤ`-indexed filtration. -/
@[stacks 0121]
structure FilteredObject where
  /-- The underlying object. -/
  obj : C
  /-- The decreasing filtration on the underlying object. -/
  filtration : DecreasingFiltration obj

/-- Construct a filtered object from an object and a decreasing filtration on it. -/
def FilteredObject.ofFiltration (obj : C) (filtration : DecreasingFiltration obj) :
    FilteredObject C :=
  ⟨obj, filtration⟩

/-- Notation for the type of filtered objects. -/
scoped notation "Fil(" C ")" => FilteredObject C

variable {C}

namespace FilteredObject

variable (A : FilteredObject C)

/-- The underlying object of the `p`-th filtration stage. -/
noncomputable abbrev stage (p : ℤ) : C := A.filtration.stage p

/-- Consecutive filtration stages satisfy
`A.filtration.stage (p + 1) ≤ A.filtration.stage p`. -/
theorem succ_le (p : ℤ) : A.filtration.stage (p + 1) ≤ A.filtration.stage p :=
  A.filtration.succ_le p

/-- The canonical inclusion from stage `p + 1` to stage `p`. -/
noncomputable abbrev succInclusion (p : ℤ) : A.stage (p + 1) ⟶ A.stage p :=
  A.filtration.succInclusion p

end FilteredObject

end CategoryTheory
