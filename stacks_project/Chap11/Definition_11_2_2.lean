/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Defs
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 11.2.2: a skew field is the canonical mathlib typeclass `DivisionRing`, namely a
possibly noncommutative ring with identity, with `1 ≠ 0`, in which every nonzero element admits a
multiplicative inverse. -/
@[stacks 0740]
recall DivisionRing
