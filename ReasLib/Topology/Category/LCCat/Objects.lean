/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Category.TopCat.Basic
public import ReasLib.Topology.Compactness.LocallyCompact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Hausdorff locally compact spaces

This file defines the object property of Hausdorff locally compact spaces and its canonical
full subcategory of `TopCat`. Limit constructions and covering families live in separate files.
-/

@[expose] public section

universe u

open CategoryTheory

namespace LCCat

/-- The object property on `TopCat` selecting Hausdorff locally compact spaces. -/
@[stacks 09WZ "Hausdorff locally compact spaces"]
abbrev property : ObjectProperty TopCat.{u} :=
  fun X ↦ T2Space X ∧ LocallyCompactSpace X

/-- In a Hausdorff space, the locally compact and weakly locally compact formulations of
`LCCat.property` agree. -/
theorem iff_weaklyLocallyCompact (X : TopCat.{u}) :
    property X ↔ T2Space X ∧ WeaklyLocallyCompactSpace X := sorry

end LCCat

/-- The full subcategory of `TopCat` on Hausdorff locally compact spaces. -/
@[stacks 09WZ "the category LC"]
abbrev LCCat : Type (u + 1) :=
  LCCat.property.FullSubcategory

namespace LCCat

/-- Bundle a Hausdorff locally compact topological space as an object of `LCCat`. -/
@[stacks 09WZ "bundling a Hausdorff locally compact space"]
abbrev of (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] : LCCat.{u} :=
  ⟨TopCat.of X, ⟨inferInstance, inferInstance⟩⟩

/-- The canonical inclusion of `LCCat` into `TopCat`. -/
@[stacks 09WZ "canonical inclusion of LCCat into TopCat"]
abbrev toTopCat : LCCat.{u} ⥤ TopCat.{u} :=
  property.ι

/-- The underlying space of an object of `LCCat` is Hausdorff. -/
@[stacks 09WZ "Hausdorff instance on LCCat objects", instance]
instance instT2SpaceObj (X : LCCat.{u}) : T2Space X.obj := sorry

/-- The underlying space of an object of `LCCat` is locally compact. -/
@[stacks 09WZ "locally compact instance on LCCat objects", instance]
instance instLocallyCompactSpaceObj (X : LCCat.{u}) : LocallyCompactSpace X.obj := sorry

end LCCat
