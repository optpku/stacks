/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Noetherian
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Definition 12.9.3 (1): `isNoetherianObject` is the canonical object property for the ascending
chain condition on subobjects. -/
@[stacks 0FCG]
#check (isNoetherianObject : ObjectProperty C)

#check @IsNoetherianObject C
#check isNoetherianObject_iff_monotone_chain_condition

/- Definition 12.9.3 (2): the source's category-level condition is objectwise Noetherianity.  This
does not add the essential-smallness field carried by mathlib's stronger class `Noetherian C`. -/
#check ∀ X : C, IsNoetherianObject X
#check Noetherian C

end CategoryTheory
