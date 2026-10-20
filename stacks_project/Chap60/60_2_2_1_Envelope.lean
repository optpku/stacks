/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope

open CategoryTheory

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  {I : Ideal A} (gamma : DividedPowers I) (f : A →+* B)
  {J : Ideal B} (hIJ : Ideal.map f I ≤ J)

/- The promoted envelope structure is available from the source-facing module. -/
#check DividedPowerEnvelope

/- The promoted envelope sequence has the expected composable-arrows type. -/
#check (DividedPowerEnvelope.sequence gamma f hIJ :
  DividedPowerEnvelope I gamma f J hIJ → ComposableArrows CommRingCat 2)

/- The promoted sequence specification has the expected quotient-map conclusion. -/
#check (DividedPowerEnvelope.sequence_hom_eq gamma f hIJ :
  ∀ E : DividedPowerEnvelope I gamma f J hIJ,
    E.sequence.hom = CommRingCat.ofHom (Ideal.Quotient.mk J))
