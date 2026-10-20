module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

universe u

namespace PrimeSpectrum

/-- The image of the spectrum map of a finite extension contains a nonempty open subset. -/
theorem exists_isOpen_subset_range_comap_of_moduleFinite
    (k : Type u) {A B : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Module.Finite A B] :
    ∃ U : Set (PrimeSpectrum A),
      IsOpen U ∧ U.Nonempty ∧
        U ⊆ Set.range (PrimeSpectrum.comap (algebraMap A B)) := sorry

/-- The image of the spectrum map contains a nonempty open subset when the induced fraction-field map is finite. -/
theorem exists_isOpen_subset_range_comap_of_finiteDimensional_fractionRing
    (k : Type u) {A B : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B]
    (hfin :
      (IsFractionRing.map (FaithfulSMul.algebraMap_injective A B) :
        FractionRing A →+* FractionRing B).Finite) :
    ∃ U : Set (PrimeSpectrum A),
      IsOpen U ∧ U.Nonempty ∧
        U ⊆ Set.range (PrimeSpectrum.comap (algebraMap A B)) := sorry

/-- The image of the spectrum map for an injective finite-type extension of domains contains a nonempty open subset. -/
theorem exists_isOpen_subset_range_comap_of_finiteType_domain
    (k : Type u) {A B : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] :
    ∃ U : Set (PrimeSpectrum A),
      IsOpen U ∧ U.Nonempty ∧
        U ⊆ Set.range (PrimeSpectrum.comap (algebraMap A B)) := sorry

end PrimeSpectrum
