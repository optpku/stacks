/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Integral
public import ReasLib.RingTheory.Pullback.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral maps in surjective ring pullbacks

The projection from a surjective ring pullback to the base-changed factor is integral whenever
the original map to the common target is integral.

@stack 0E1S
-/

@[expose] public section

universe u

noncomputable section

namespace SurjectiveRingPullbackSituation

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/-- In a surjective ring-pullback situation, integrality of `B -> A` implies integrality of the
canonical projection `B x_A A' -> A'`. -/
@[stacks 0E1S "integrality of a surjective pullback projection"]
theorem bprimeToAprime_isIntegral (S : SurjectiveRingPullbackSituation B A A')
    (hBA : S.toA.IsIntegral) :
    S.bprimeToAprime.IsIntegral := sorry

end SurjectiveRingPullbackSituation
