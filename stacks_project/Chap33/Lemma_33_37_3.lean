/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair.Valuation

@[expose] public section

universe u

/-
Lemma 33.37.3 states that the tensor comparison for two subrings of a common
fraction field is nonsurjective exactly when a discrete valuation subring
contains both subrings.
-/
@[stacks 09N0] #check
  (FractionRing.SubringPair.tensorToAmbient_not_surjective_iff_hasDominatingDVR :
    ∀ {K : Type u} [Field K] (P : FractionRing.SubringPair K) [IsNoetherianRing P.left],
      ringKrullDim P.left = 1 →
        (¬ Function.Surjective P.tensorToAmbient ↔
          ∃ V : ValuationSubring K,
            P.left ≤ V.toSubring ∧ P.right ≤ V.toSubring ∧ IsDiscreteValuationRing V))
