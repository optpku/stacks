module

public import ReasLib.RingTheory.Completion.Quotient
public import ReasLib.RingTheory.Pullback.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Complete Noetherian Surjective Pullbacks

The fiber product of two complete Noetherian local rings over a common quotient is again complete
local and Noetherian.

@stack 09Q8
-/

@[expose] public section

universe u

namespace SurjectiveRingPullbackSituation

variable {R S S' : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [IsCompleteLocalRing S] [IsNoetherianRing S]
variable [IsCompleteLocalRing S'] [IsNoetherianRing S']

/-- Lemma 15.39.4 (1) (Stacks `09Q8`): if both maps to the common target are surjective, the
fiber-product ring is complete local. -/
@[stacks 09Q8 "complete local pullback"]
theorem bprime_isCompleteLocalRing_of_surjective
    (T : SurjectiveRingPullbackSituation S R S')
    (h_toA : Function.Surjective T.toA) [Nontrivial R] :
    IsCompleteLocalRing T.Bprime := sorry

/-- Lemma 15.39.4 (2) (Stacks `09Q8`): under the same hypotheses, the fiber-product ring is
Noetherian. -/
@[stacks 09Q8 "Noetherian pullback"]
theorem bprime_isNoetherianRing_of_surjective
    (T : SurjectiveRingPullbackSituation S R S')
    (h_toA : Function.Surjective T.toA) [Nontrivial R] :
    IsNoetherianRing T.Bprime := sorry

end SurjectiveRingPullbackSituation
