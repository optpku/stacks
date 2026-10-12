/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.OpenSubset
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.61.1

The reusable owner is `PrimeSpectrum.infinite_coe_of_ne_bot_of_two_le_ringKrullDim`.

@stack 02IG
-/

/- Lemma 10.61.1: if `R` is a Noetherian local domain of Krull dimension at least `2`, then every
nonempty open subset of `Spec(R)` is infinite. -/
@[stacks 02IG]
#check @PrimeSpectrum.infinite_coe_of_ne_bot_of_two_le_ringKrullDim

/- Predicate-form companion. -/
@[stacks 02IG "predicate-form infinitude criterion"]
#check @PrimeSpectrum.infinite_coe_of_ne_bot_of_not_krullDimLE_one
