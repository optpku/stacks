/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Lift
public import ReasLib.CategoryTheory.Localization.Lifting.Computation

/-!
# Computation for bounded finite filtered localization lifts

The bounded-below, bounded-above, and bounded quotient lifts are all instances of
`Localization.Lifting`.  Their naturality and map formulas are therefore supplied uniformly by
`Localization.Lifting.iso.hom_naturality`, `Localization.Lifting.iso.inv_naturality`, and
`Localization.Lifting.map_localization`; no boundedness-specific copies are needed.
-/

@[expose] public section
