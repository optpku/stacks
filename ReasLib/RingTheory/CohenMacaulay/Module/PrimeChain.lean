module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module

/-!
# Maximal Prime Chains for Cohen--Macaulay Modules

This leaf owns the dimension formula for a maximal prime chain when a
Cohen--Macaulay module has full support. The module condition is an instance,
so downstream applications only provide the support hypothesis and the chain
being measured.
-/

@[expose] public section

universe u v

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

/-- Lemma 10.103.9 (Stacks tag `0AAE`): every maximal prime chain has length
`ringKrullDim R` when a finite Cohen--Macaulay `R`-module has full support. -/
@[stacks 0AAE]
theorem ringKrullDim_eq_length_of_maximal_chain
    (hsupp : Module.support R M = Set.univ)
    (p : LTSeries (PrimeSpectrum R))
    (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    ringKrullDim R = p.length := sorry

end Module.CohenMacaulay
