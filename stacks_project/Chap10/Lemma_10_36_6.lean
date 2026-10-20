/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.36.6

@stack 00GN
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.6: if `R → S` and `S → T` are integral ring homomorphisms, then the composite
ring homomorphism `R → T` is integral. This is exactly the canonical mathlib theorem
`RingHom.IsIntegral.trans`. -/
@[stacks 00GN]
#check @RingHom.IsIntegral.trans
