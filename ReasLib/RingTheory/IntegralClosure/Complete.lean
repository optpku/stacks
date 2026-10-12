/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complete integral closures

`completeIntegralClosure R S` is Mathlib's canonical subalgebra of almost
integral elements.  This leaf exposes the bottom-subalgebra criterion and its
fraction-ring consequence without introducing a parallel ``completely normal''
predicate.
-/

universe u v

namespace CompleteIntegralClosure

/-- The complete integral closure is bottom exactly when every almost integral
element comes from the base algebra map. -/
@[stacks 00GW "complete integral closure criterion"]
theorem eq_bot_iff {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] :
    completeIntegralClosure R S = ⊥ ↔
      ∀ x : S, IsAlmostIntegral R x → ∃ y : R, algebraMap R S y = x := sorry
/- Proof strategy: rewrite membership in `completeIntegralClosure` with
`mem_completeIntegralClosure`, then use `Algebra.mem_bot` and `Set.mem_range`. -/

/-- If the complete integral closure in a fraction ring is bottom, the base
ring is integrally closed. -/
@[stacks 00GW "complete normality implies integral closedness"]
theorem isIntegrallyClosed_of_eq_bot
    {R : Type u} {K : Type v} [CommRing R] [CommRing K]
    [Algebra R K] [IsFractionRing R K]
    (h : completeIntegralClosure R K = ⊥) :
    IsIntegrallyClosed R := sorry
/- Proof strategy: combine `integralClosure_le_completeIntegralClosure` with
`IsIntegrallyClosed.integralClosure_eq_bot_iff`. -/

end CompleteIntegralClosure
