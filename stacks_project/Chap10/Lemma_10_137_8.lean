/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.StandardSmooth
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Lemma 10.137.8 (Tag 00T9): the composition of two standard smooth ring maps is standard smooth.
This is exactly the canonical theorem `RingHom.IsStandardSmooth.comp`.

@stack 00T9
-/
@[stacks 00T9]
#check @RingHom.IsStandardSmooth.comp
