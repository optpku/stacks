/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module

/-!
# Dimension Formulas for Cohen--Macaulay Modules

This leaf owns local-to-global Krull-dimension formulas obtained from a
full-support Cohen--Macaulay module. It is independent of the chapter proof
route through maximal chains.
-/

@[expose] public section

universe u v

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

/-- Lemma 10.103.10 (Stacks tag `0AAF`): for a full-support Cohen--Macaulay
module, the dimension of `R` is the sum of the dimensions at any prime and of
its prime quotient. -/
@[stacks 0AAF]
theorem ringKrullDim_eq_localizationAtPrime_add_quotient_of_fullSupport
    (hsupp : Module.support R M = Set.univ) (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) := sorry

end Module.CohenMacaulay
