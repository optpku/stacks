/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DedekindDomain.IdealFactorization
import StacksCheckRecall

/-!
# Characterizations of Dedekind domains

@stack 034X
-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

/- Lemma 10.120.17 (1): clauses (1) and (3) of Stacks `034X`, using Mathlib's canonical
Dedekind-domain owner: a Noetherian normal domain of Krull dimension at most one. -/
@[stacks 034X "(1) ↔ (3)"]
#check (isDedekindDomain_iff_noetherian_dimensionLEOne_isIntegrallyClosed R :
  IsDedekindDomain R ↔
    IsDomain R ∧ IsNoetherianRing R ∧ Ring.DimensionLEOne R ∧ IsIntegrallyClosed R)

/- Lemma 10.120.17 (2): clauses (1) and (2) of Stacks `034X` say equivalently that the ring is a
Noetherian domain whose localization at every nonzero maximal ideal is a DVR. -/
@[stacks 034X "(1) ↔ (2)"]
#check (IsDedekindDomain.iff_localizationAtMaximal (R := R) :
  IsDedekindDomain R ↔
    ∃ (_ : IsDomain R) (_ : IsNoetherianRing R),
      ∀ m : MaximalSpectrum R, m.asIdeal ≠ ⊥ →
        IsDiscreteValuationRing (Localization.AtPrime m.asIdeal))

#check @isDedekindDomain_iff_isDedekindDomainDvr
#check @IsDedekindRing.toIsNoetherian
#check @IsDedekindRing.toDimensionLEOne
#check @IsDedekindRing.toIsIntegralClosure
