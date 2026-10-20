/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module
import StacksCheckRecall

/-!
# Definition 10.104.1

@stack 00N8
-/

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Definition 10.104.1: a Noetherian local ring is Cohen-Macaulay if it is Cohen-Macaulay as a
module over itself. -/
@[stacks 00N8]
#check (Module.CohenMacaulay R R)
