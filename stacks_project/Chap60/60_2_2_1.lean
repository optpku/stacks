/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.DividedPowers.Envelope

open CategoryTheory

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  {I : Ideal A} (gamma : DividedPowers I) (f : A →+* B)
  {J : Ideal B} (hIJ : Ideal.map f I ≤ J)

/- 60.2.2.1: the divided-power envelope is displayed by the composable chain
`B ⟶ D ⟶ B ⧸ J`. -/
@[stacks 07HA] #check (DividedPowerEnvelope.sequence gamma f hIJ :
  DividedPowerEnvelope I gamma f J hIJ → ComposableArrows CommRingCat 2)
