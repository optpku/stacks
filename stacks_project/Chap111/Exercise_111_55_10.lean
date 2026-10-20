module

import ReasLib.RingTheory.Spectrum.Prime.Chevalley.Domain
import StacksCheckRecall

universe u

/- Exercise 111.55.10 (1) -/
@[stacks 07DP] #check (PrimeSpectrum.exists_isOpen_subset_range_comap_of_moduleFinite :
  ∀ (k : Type u) {A B : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Module.Finite A B],
    ∃ U : Set (PrimeSpectrum A),
      IsOpen U ∧ U.Nonempty ∧
        U ⊆ Set.range (PrimeSpectrum.comap (algebraMap A B)))

/- Exercise 111.55.10 (2) -/
@[stacks 07DP] #check (PrimeSpectrum.exists_isOpen_subset_range_comap_of_finiteDimensional_fractionRing :
  ∀ (k : Type u) {A B : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B]
    (hfin :
      (IsFractionRing.map (FaithfulSMul.algebraMap_injective A B) :
        FractionRing A →+* FractionRing B).Finite),
    ∃ U : Set (PrimeSpectrum A),
      IsOpen U ∧ U.Nonempty ∧
        U ⊆ Set.range (PrimeSpectrum.comap (algebraMap A B)))

/- Exercise 111.55.10 (3) -/
@[stacks 07DP] #check (PrimeSpectrum.exists_isOpen_subset_range_comap_of_finiteType_domain :
  ∀ (k : Type u) {A B : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B],
    ∃ U : Set (PrimeSpectrum A),
      IsOpen U ∧ U.Nonempty ∧
        U ⊆ Set.range (PrimeSpectrum.comap (algebraMap A B)))
