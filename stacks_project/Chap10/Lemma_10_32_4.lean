/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent.Unit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.32.4

@stack 0AMG

Units are detected after quotienting by a locally nilpotent ideal.
-/

@[stacks 0AMG "units modulo a locally nilpotent ideal"]
#check @Ideal.IsLocallyNilpotent.isUnit_iff_quotient_mk
