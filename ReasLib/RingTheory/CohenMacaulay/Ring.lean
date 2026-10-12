/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition

@[expose] public section

/-!
# Cohen-Macaulay Rings

A ring is Cohen-Macaulay if it is Noetherian and every localization at a prime ideal is a
Cohen-Macaulay local ring (i.e., the ring viewed as a module over itself is Cohen-Macaulay).

## Main definitions

* `CohenMacaulayRing` — Noetherian ring with CM localizations at all primes.

## Main results

* `CohenMacaulayRing.localizedRing_cohenMacaulay` — localization is CM.
* `CohenMacaulayRing.localizedRing_depth_eq_krullDim` — depth = dim at each localization.
* `CohenMacaulayRing.serreS` — a CM ring satisfies (S_k) for all k.
* `CohenMacaulayRing.of_serreS` — converse: (S_k) for all k implies CM.
-/

universe u

open PrimeSpectrum
open scoped ENat

section

variable (R : Type u) [CommRing R]

/-- A ring is Cohen-Macaulay if it is Noetherian and every localization at a prime ideal is a
Cohen-Macaulay local ring. -/
@[stacks 00NC]
class CohenMacaulayRing : Prop where
  /-- The ring is Noetherian. -/
  toIsNoetherian : IsNoetherianRing R
  /-- The self-module is Cohen-Macaulay at every prime. -/
  toLocallyCohenMacaulay :
    @Module.LocallyCohenMacaulay R _ toIsNoetherian R _ _

/-- A Cohen-Macaulay ring is Noetherian. -/
instance [h : CohenMacaulayRing R] : IsNoetherianRing R := h.toIsNoetherian

namespace CohenMacaulayRing

/-- A Cohen--Macaulay ring is locally Cohen--Macaulay as a module over itself. -/
instance locallyCohenMacaulay [h : CohenMacaulayRing R] :
    Module.LocallyCohenMacaulay R R :=
  h.toLocallyCohenMacaulay

/-- Every localization of a Cohen-Macaulay ring is a Cohen-Macaulay self-module. -/
theorem localizedRing_cohenMacaulay (p : PrimeSpectrum R)
    [h : CohenMacaulayRing R] :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  simpa using h.toLocallyCohenMacaulay.localizedModule_cohenMacaulay p

/-- Every localization of a Cohen-Macaulay ring satisfies depth = dim. -/
theorem localizedRing_depth_eq_krullDim (p : PrimeSpectrum R) [h : CohenMacaulayRing R] :
    WithBot.some (moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) =
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  rw [← Module.supportDim_self_eq_ringKrullDim]
  exact (localizedRing_cohenMacaulay R p).supportDim_eq_moduleDepth.symm

/-- A Cohen-Macaulay ring satisfies Serre's condition `(S_k)` for every `k`. -/
theorem serreS (k : ℕ) [h : CohenMacaulayRing R] : SerreConditionS R k := sorry

/-- A Noetherian ring is Cohen-Macaulay if it satisfies Serre's condition `(S_k)` for every
`k`. -/
theorem of_serreS [IsNoetherianRing R] (hS : ∀ k : ℕ, SerreConditionS R k) :
    CohenMacaulayRing R := sorry

end CohenMacaulayRing

end
