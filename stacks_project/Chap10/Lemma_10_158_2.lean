/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.Frobenius
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.158.2

The source statement is the standard Frobenius criterion for the universal
Kähler derivation over a perfect field of positive characteristic.

@stack 031W
-/

@[stacks 031W]
#check @KaehlerDifferential.Frobenius.d_eq_zero_iff_exists_pth_root
