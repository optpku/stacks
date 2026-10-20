/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

/-- An object of `C` equipped with an explicit decreasing `ℤ`-indexed filtration. -/
structure FilteredObject.Data where
  /-- The underlying object. -/
  obj : C
  /-- The decreasing filtration on the underlying object. -/
  filtration : DecreasingFiltration obj

/-- Construct filtration data from an ambient object and a decreasing filtration. -/
def FilteredObject.Data.ofFiltration (obj : C) (filtration : DecreasingFiltration obj) :
    FilteredObject.Data C :=
  ⟨obj, filtration⟩

/-- The category-facing type of objects equipped with decreasing integer-indexed filtrations. -/
@[stacks 0121]
def FilteredObject := FilteredObject.Data C

/-- Notation for the type of filtered objects. -/
scoped notation "Fil(" C ")" => FilteredObject C

variable {C}

namespace FilteredObject

/-- View explicit filtration data as a filtered object. -/
def fromData (A : Data C) : FilteredObject C := A

/-- Recover the explicit ambient object and filtration of a filtered object. -/
def toData (A : FilteredObject C) : Data C := A

/-- Recovering the data of its categorical view returns the original data. -/
@[simp] theorem toData_fromData (A : Data C) : (fromData A).toData = A := rfl

/-- The categorical view of a filtered object's data is the original filtered object. -/
@[simp] theorem fromData_toData (A : FilteredObject C) : fromData A.toData = A := rfl

/-- The ambient object underlying a filtered object. -/
abbrev obj (A : FilteredObject C) : C := A.toData.obj

/-- The decreasing filtration underlying a filtered object. -/
abbrev filtration (A : FilteredObject C) : DecreasingFiltration A.obj :=
  A.toData.filtration

/-- Construct a filtered object from its ambient object and filtration. -/
def mk (obj : C) (filtration : DecreasingFiltration obj) : FilteredObject C :=
  fromData (Data.ofFiltration C obj filtration)

/-- Construct a filtered object from an object and a decreasing filtration on it. -/
def ofFiltration (C : Type u) [Category.{v} C] (obj : C)
    (filtration : DecreasingFiltration obj) : FilteredObject C :=
  mk obj filtration

namespace Data

/-- The ambient object of a stage of explicit filtration data. -/
noncomputable abbrev stage (A : Data C) (p : ℤ) : C := A.filtration.stage p

/-- Consecutive stages of explicit filtration data are decreasing. -/
theorem succ_le (A : Data C) (p : ℤ) : A.filtration.stage (p + 1) ≤ A.filtration.stage p :=
  A.filtration.succ_le p

/-- The canonical inclusion between consecutive stages of explicit filtration data. -/
noncomputable abbrev succInclusion (A : Data C) (p : ℤ) : A.stage (p + 1) ⟶ A.stage p :=
  A.filtration.succInclusion p

end Data

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
