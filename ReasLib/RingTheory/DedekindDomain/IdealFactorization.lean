/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime-ideal factorizations in Dedekind domains

This file separates finite prime-ideal factorizations from the Dedekind-domain characterization
that they induce.  The factorization predicates are available over commutative semirings, while
the source-facing Dedekind predicate is connected to Mathlib's canonical `IsDedekindDomain` and
`IsDedekindDomainDvr` owners.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- A multiset is a prime factorization of an ideal when all of its entries are nonzero prime
ideals and their product is the given ideal. -/
@[stacks 034W "prime factorization"]
def IsPrimeFactorization (I : Ideal R) (f : Multiset (Ideal R)) : Prop :=
  (∀ P ∈ f, P ≠ ⊥ ∧ P.IsPrime) ∧ f.prod = I

namespace IsPrimeFactorization

/-- Every factor occurring in a prime factorization is nonzero. -/
@[stacks 034W "nonzero factor"]
theorem ne_bot_of_mem {I P : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) (hP : P ∈ f) : P ≠ ⊥ := sorry

/-- Every factor occurring in a prime factorization is a prime ideal. -/
@[stacks 034W "prime factor"]
theorem isPrime_of_mem {I P : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) (hP : P ∈ f) : P.IsPrime := sorry

/-- The product recorded by a prime factorization is the factored ideal. -/
@[stacks 034W "factorization product"]
theorem prod_eq {I : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) : f.prod = I := sorry

/-- A nonzero prime ideal is its own one-term prime factorization. -/
@[stacks 034W "singleton factorization"]
theorem singleton {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime) :
    IsPrimeFactorization P {P} := sorry

/-- If a prime ideal contains an ideal represented by a prime factorization, then it contains
one of the factors. -/
@[stacks 034W "factor below a prime"]
theorem exists_le_of_le_prime {I P : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) (hP : P.IsPrime) (hIP : I ≤ P) :
    ∃ Q ∈ f, Q ≤ P := sorry

end IsPrimeFactorization

/-- Every nonzero ideal has a unique multiset factorization into nonzero prime ideals. -/
@[stacks 034W "unique prime factorization"]
def HasUniquePrimeFactorization (R : Type u) [CommSemiring R] : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃! f : Multiset (Ideal R), I.IsPrimeFactorization f

namespace HasUniquePrimeFactorization

/-- Unique prime factorization supplies a prime factorization of each nonzero ideal. -/
@[stacks 034W "factorization existence"]
theorem exists_factorization (h : HasUniquePrimeFactorization R)
    {I : Ideal R} (hI : I ≠ ⊥) :
    ∃ f : Multiset (Ideal R), I.IsPrimeFactorization f := sorry

/-- Two prime factorizations of the same nonzero ideal agree as multisets. -/
@[stacks 034W "factorization uniqueness"]
theorem unique (h : HasUniquePrimeFactorization R) {I : Ideal R}
    (hI : I ≠ ⊥) {f g : Multiset (Ideal R)}
    (hf : I.IsPrimeFactorization f) (hg : I.IsPrimeFactorization g) : f = g := sorry

end HasUniquePrimeFactorization

end Ideal

/-- Definition 10.120.14 (Stacks `034W`): a Dedekind domain, expressed by unique
factorization of every nonzero ideal into nonzero prime ideals. -/
@[stacks 034W]
def IsDedekindDomainByFactorization (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ Ideal.HasUniquePrimeFactorization R

namespace IsDedekindDomain

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

open UniqueFactorizationMonoid

/-- Mathlib's normalized factors of a nonzero ideal form its canonical prime factorization. -/
@[stacks 034W "normalized factors"]
theorem isPrimeFactorization_normalizedFactors {I : Ideal R} (hI : I ≠ ⊥) :
    I.IsPrimeFactorization (normalizedFactors I) := sorry

/-- The canonical Dedekind-domain owner supplies unique prime factorizations of nonzero ideals. -/
@[stacks 034W "canonical factorization"]
theorem hasUniquePrimeFactorization : Ideal.HasUniquePrimeFactorization R := sorry

/-- A canonical Dedekind domain satisfies the factorization formulation. -/
@[stacks 034W "canonical construction"]
theorem byFactorization : IsDedekindDomainByFactorization R := sorry

end IsDedekindDomain

/-- The ideal-factorization formulation is equivalent to Mathlib's canonical Dedekind-domain
owner. -/
@[stacks 034W "canonical bridge"]
theorem isDedekindDomain_iff_isDedekindDomainByFactorization
    (R : Type u) [CommRing R] :
    IsDedekindDomain R ↔ IsDedekindDomainByFactorization R := sorry

/-- Lemma 10.120.17 (1): clauses (1) and (3) of Stacks `034X` identify unique prime-ideal
factorization with a Noetherian normal domain of Krull dimension at most one. -/
@[stacks 034X "Noetherian normal characterization"]
theorem isDedekindDomainByFactorization_iff (R : Type u) [CommRing R] :
    IsDedekindDomainByFactorization R ↔
      IsDomain R ∧ IsNoetherianRing R ∧ Ring.DimensionLEOne R ∧ IsIntegrallyClosed R := sorry

namespace IsDedekindDomainByFactorization

variable {R : Type u} [CommRing R]

/-- Lemma 10.120.17 (2): clauses (1) and (2) of Stacks `034X` give the source-faithful
characterization using the localizations at nonzero maximal ideals. -/
@[stacks 034X "local DVR characterization"]
theorem iff_localizationAtMaximal :
    IsDedekindDomainByFactorization R ↔
      ∃ (_ : IsDomain R) (_ : IsNoetherianRing R),
        ∀ m : MaximalSpectrum R, m.asIdeal ≠ ⊥ →
          IsDiscreteValuationRing (Localization.AtPrime m.asIdeal) := sorry

/-- The factorization formulation includes the domain condition. -/
@[stacks 034W "domain projection"]
theorem isDomain (h : IsDedekindDomainByFactorization R) : IsDomain R := sorry

/-- The factorization formulation includes unique prime factorization of nonzero ideals. -/
@[stacks 034W "factorization projection"]
theorem hasUniquePrimeFactorization (h : IsDedekindDomainByFactorization R) :
    Ideal.HasUniquePrimeFactorization R := sorry

/-- A ring satisfying the factorization formulation is Noetherian. -/
@[stacks 034X "Noetherian projection"]
theorem isNoetherianRing (h : IsDedekindDomainByFactorization R) :
    IsNoetherianRing R := sorry

/-- A ring satisfying the factorization formulation has Krull dimension at most one. -/
@[stacks 034X "dimension projection"]
theorem dimensionLEOne (h : IsDedekindDomainByFactorization R) :
    Ring.DimensionLEOne R := sorry

/-- A ring satisfying the factorization formulation is integrally closed. -/
@[stacks 034X "normality projection"]
theorem isIntegrallyClosed (h : IsDedekindDomainByFactorization R) :
    IsIntegrallyClosed R := sorry

end IsDedekindDomainByFactorization

/-- Under an ambient domain instance, the factorization formulation is equivalent to Mathlib's
local-DVR Dedekind-domain owner. -/
@[stacks 034X "canonical local-DVR bridge"]
theorem isDedekindDomainByFactorization_iff_isDedekindDomainDvr
    (R : Type u) [CommRing R] [IsDomain R] :
    IsDedekindDomainByFactorization R ↔ IsDedekindDomainDvr R := sorry
