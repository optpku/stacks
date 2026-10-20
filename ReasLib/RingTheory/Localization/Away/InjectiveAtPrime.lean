/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Injective Away Neighborhoods of Prime Localizations

Under standard finiteness or reducedness hypotheses, a prime localization is approached by an
injective map from one principal localization.
-/

universe u

namespace Localization.AtPrime

/-- If `R` is a domain, Noetherian, or reduced with finitely many minimal primes, then for every
prime ideal `p` some canonical map `R_f → R_p`, with `f ∉ p`, is injective. -/
@[stacks 0BX1]
theorem exists_awayMap_injective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (h : IsDomain R ∨ IsNoetherianRing R ∨
      (IsReduced R ∧ (minimalPrimes R).Finite)) :
    ∃ f : p.primeCompl,
      Function.Injective
        (awayLift (algebraMap R (Localization.AtPrime p)) f.1
          (IsLocalization.map_units (Localization.AtPrime p) f)) := sorry

end Localization.AtPrime
