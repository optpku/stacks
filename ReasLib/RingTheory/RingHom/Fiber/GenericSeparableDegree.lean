module

public import Mathlib.FieldTheory.SeparableDegree
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.QuasiFinite

/-!
# Generic separable degrees of finite local-ring comparisons

This module records the separable degree of the reduced generic fibre as a
canonical sum over its prime spectrum.  It also gives a choice-independent
specification for the value obtained from strict-henselization comparisons.
-/

@[expose] public section

noncomputable section

open Ideal

universe u v

namespace RingHom

/-- The generic separable degree of a finite ring homomorphism at a prime is
the sum of the finite separable degrees of the residue fields of its fibre. -/
noncomputable def genericSepDegreeAt {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Finite) (p : PrimeSpectrum A) : ℕ :=
  -- Local instance justification (defeq pin): the fibre must use the algebra structure induced by `φ`.
  letI : Algebra A B := φ.toAlgebra
  -- Local instance justification (defeq pin): finiteness must refer to the same explicit-map algebra structure.
  letI : Module.Finite A B := hφ
  -- Local instance justification (noncanonical choice): `Finset.univ` enumerates the finite prime spectrum only inside this sum.
  letI : Fintype (PrimeSpectrum (p.asIdeal.Fiber B)) := Fintype.ofFinite _
  ∑ q : PrimeSpectrum (p.asIdeal.Fiber B),
    Field.finSepDegree p.asIdeal.ResidueField q.asIdeal.ResidueField

/-- The generic separable degree is independent of the proof that the ring
homomorphism is finite. -/
theorem genericSepDegreeAt_proof_irrel {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ hφ' : φ.Finite)
    (p : PrimeSpectrum A) :
    φ.genericSepDegreeAt hφ p = φ.genericSepDegreeAt hφ' p := sorry

namespace QuasiFinite

/-- A compatible local map between strict henselizations of the source and
target of an essentially finite-type, quasi-finite local ring homomorphism is finite. -/
theorem strictHenselizationComparison_finite
    {A : Type u} {B : Type v} {Ash : Type u} {Bsh : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (hft : φ.EssFiniteType) (hqf : φ.QuasiFinite) [IsLocalHom φ]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    (comparison : Ash →+* Bsh) [IsLocalHom comparison]
    (hcomparison : comparison.comp (algebraMap A Ash) = (algebraMap B Bsh).comp φ) :
    comparison.Finite := sorry

end QuasiFinite

/-- `n` is the generic separable degree of a quasi-finite local homomorphism
when every compatible strict-henselization comparison computes `n` by the
canonical finite generic-fibre sum. -/
def IsGenericSepDegree {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (hft : φ.EssFiniteType) (hqf : φ.QuasiFinite)
    [IsLocalHom φ] (n : ℕ) : Prop :=
  ∀ {Ash : Type u} {Bsh : Type v}
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    (comparison : Ash →+* Bsh) [IsLocalHom comparison]
    (hcomparison : comparison.comp (algebraMap A Ash) = (algebraMap B Bsh).comp φ)
    (p : PrimeSpectrum Ash), p.asIdeal ∈ minimalPrimes Ash →
      n = comparison.genericSepDegreeAt
        (RingHom.QuasiFinite.strictHenselizationComparison_finite
          φ hft hqf comparison hcomparison) p

/-- The explicit strict-henselization comparison characterization of
`RingHom.IsGenericSepDegree`. -/
theorem isGenericSepDegree_iff {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (hft : φ.EssFiniteType) (hqf : φ.QuasiFinite)
    [IsLocalHom φ] (n : ℕ) :
    φ.IsGenericSepDegree hft hqf n ↔
      ∀ {Ash : Type u} {Bsh : Type v}
        [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
        [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
        (comparison : Ash →+* Bsh) [IsLocalHom comparison]
        (hcomparison : comparison.comp (algebraMap A Ash) = (algebraMap B Bsh).comp φ)
        (p : PrimeSpectrum Ash), p.asIdeal ∈ minimalPrimes Ash →
          n = comparison.genericSepDegreeAt
            (RingHom.QuasiFinite.strictHenselizationComparison_finite
              φ hft hqf comparison hcomparison) p := sorry

namespace IsGenericSepDegree

/-- Two generic separable degrees computed from the same explicit compatible
strict-henselization comparison and minimal prime are equal. -/
theorem eq_of_comparison {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (hft : φ.EssFiniteType) (hqf : φ.QuasiFinite)
    [IsLocalHom φ] {m n : ℕ}
    (hm : φ.IsGenericSepDegree hft hqf m)
    (hn : φ.IsGenericSepDegree hft hqf n)
    {Ash : Type u} {Bsh : Type v}
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    (comparison : Ash →+* Bsh) [IsLocalHom comparison]
    (hcomparison : comparison.comp (algebraMap A Ash) = (algebraMap B Bsh).comp φ)
    (p : PrimeSpectrum Ash) (hp : p.asIdeal ∈ minimalPrimes Ash) :
    m = n := sorry

end IsGenericSepDegree

end RingHom
