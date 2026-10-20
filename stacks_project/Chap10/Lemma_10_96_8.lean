/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.IdealGenerators
import StacksCheckRecall

@[expose] public section

/-!
@stack 090T
# Lemma 10.96.8

The finite-generated ideal monotonicity theorem is owned by
`ReasLib.RingTheory.AdicCompletion.IdealGenerators`.
-/

/- Lemma 10.96.8 (Stacks 090T): completeness descends along an inclusion of
finitely generated ideals. -/
@[stacks 090T]
#check @IsAdicComplete.of_le_of_fg
