/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.RingTheory.Etale.Finite
import StacksCheckRecall

universe u

/- Example 58.5.1 -/
@[stacks 0BN8] #check (CommAlgCat.FiniteEtale.equivOfIsSepClosed :
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω],
    (CommAlgCat.FiniteEtale Ω)ᵒᵖ ≌ FintypeCat)
