/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Finite
import StacksCheckRecall

@[expose] public section

universe v u

/- Definition 111.30.4: for an abelian category `𝒜`, `Fil^f(𝒜)` is the full subcategory of
`Fil(𝒜)` on objects whose filtration is finite. This is the existing owner
`FilteredObject.Finite.category 𝒜`, with reusable notation `Filᶠ(𝒜)` and inclusion
`FilteredObject.Finite.inclusion`. -/
@[stacks 028B] #check (@CategoryTheory.FilteredObject.Finite.category :
  (C : Type u) → [CategoryTheory.Category.{v} C] →
    [CategoryTheory.Limits.HasZeroObject C] → Type (max u v))
@[stacks 028B] #check @CategoryTheory.FilteredObject.Finite.inclusion
