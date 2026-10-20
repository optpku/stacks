/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Finite
import StacksCheckRecall

@[expose] public section

/- Definition 13.13.1 (`05RY`): the finite filtered category is the canonical full subcategory
`FilteredObject.Finite.category 𝒜`; the reusable notation is the neutral `Filᶠ(𝒜)` from the ReasLib
finite-filtration leaf. -/
@[stacks 05RY] #check @CategoryTheory.FilteredObject.Finite.category
@[stacks 05RY] #check @CategoryTheory.FilteredObject.Finite.inclusion
