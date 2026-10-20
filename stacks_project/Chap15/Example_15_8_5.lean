/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FittingIdeal.Free
import StacksCheckRecall

/-!
# Example 15.8.5

The source example is the finite-free computation in the intrinsic Fitting-ideal owner.

@stack 07ZB
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

@[stacks 07ZB "Fitting ideals of a finite free module"]
#check (FittingIdeal.free_eq_bot_or_top R)

@[stacks 07ZB "vanishing range for finite-free Fitting ideals"]
#check (FittingIdeal.free_eq_bot_of_lt R)

@[stacks 07ZB "unit range for finite-free Fitting ideals"]
#check (FittingIdeal.free_eq_top_of_le R)
