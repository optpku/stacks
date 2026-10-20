/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Quotient
import StacksCheckRecall

@[expose] public section

/-!
@stack 031L
-/

/- Lemma 10.138.12 [stacks 031L]: canonical recall of square-zero quotient
ascent for formally smooth algebras. -/

@[stacks 031L]
#check @Algebra.FormallySmooth.of_squareZeroIdeal_of_flat
