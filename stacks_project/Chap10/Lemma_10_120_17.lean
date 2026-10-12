/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/- Lemma 10.120.17 (1): clauses (1) and (3) of Stacks `034X` identify unique prime-ideal
factorization with a Noetherian normal domain of Krull dimension at most one. -/
@[stacks 034X "(1) ↔ (3)"]
#check (isDedekindDomainByFactorization_iff R :
  IsDedekindDomainByFactorization R ↔
    IsDomain R ∧ IsNoetherianRing R ∧ Ring.DimensionLEOne R ∧ IsIntegrallyClosed R)

/- Lemma 10.120.17 (2): clauses (1) and (2) of Stacks `034X` say equivalently that the ring is a
Noetherian domain whose localization at every nonzero maximal ideal is a DVR. -/
@[stacks 034X "(1) ↔ (2)"]
#check (IsDedekindDomainByFactorization.iff_localizationAtMaximal (R := R) :
  IsDedekindDomainByFactorization R ↔
    ∃ (_ : IsDomain R) (_ : IsNoetherianRing R),
      ∀ m : MaximalSpectrum R, m.asIdeal ≠ ⊥ →
        IsDiscreteValuationRing (Localization.AtPrime m.asIdeal))

#check @isDedekindDomainByFactorization_iff_isDedekindDomainDvr
#check @IsDedekindDomainByFactorization.isNoetherianRing
#check @IsDedekindDomainByFactorization.dimensionLEOne
#check @IsDedekindDomainByFactorization.isIntegrallyClosed
