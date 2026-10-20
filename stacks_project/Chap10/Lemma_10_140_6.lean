/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.Regular
import StacksCheckRecall

/-!
# Lemma 10.140.6

@stack 00TW
-/

@[expose] public section

/- Lemma 10.140.6 [stacks 00TW]: canonical recall of the non-nilpotence and regular-element
criteria supplied by a split Kahler differential direction. -/
@[stacks 00TW]
#check @KaehlerDifferential.not_isNilpotent_of_exists_linearMap_D_eq_one

@[stacks 00TW]
#check @KaehlerDifferential.isRegular_of_exists_linearMap_D_eq_one
