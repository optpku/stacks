/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.KrullIntersection.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Krull intersection remark

Remark 10.51.6 (Tag 00IR) consumes the reusable localized Krull-intersection API.
@stack 00IR
-/

/-
Remark 10.51.6, first clause: for a non-unit ideal `I` in a Noetherian local ring,
Krull's intersection theorem gives `⨅ n : ℕ, I ^ n = ⊥`. This is exactly the canonical
mathlib theorem `Ideal.iInf_pow_eq_bot_of_isLocalRing`.
-/
@[stacks 00IR "(1) local Krull intersection"]
#check @Ideal.iInf_pow_eq_bot_of_isLocalRing

/- Remark 10.51.6, general clause: an element in every power of `I` vanishes on a principal open
neighborhood of every prime containing `I`. -/
@[stacks 00IR]
#check @Ideal.exists_notMem_and_algebraMap_eq_zero_of_mem_iInf_pow
