/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import ReasLib.RingTheory.Topology.Adic.Basic

@[expose] public section

universe u

open Topology TopologicalSpace

namespace AlgebraicGeometry.FormalSpectrum

/-- The subspace of the prime spectrum consisting of open prime ideals. -/
abbrev OpenPrime (A : Type u) [CommRing A] [TopologicalSpace A] :=
  {p : PrimeSpectrum A // IsOpen (p.asIdeal : Set A)}

namespace OpenPrime

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The prime-spectrum point underlying an open prime ideal. -/
def toPrimeSpectrum (p : OpenPrime A) : PrimeSpectrum A := p.val

/-- The ideal underlying an open prime. -/
def asIdeal (p : OpenPrime A) : Ideal A := p.toPrimeSpectrum.asIdeal

/-- The inverse image of a quotient prime modulo an open ideal is open. -/
theorem isOpen_comap_quotient [IsTopologicalRing A] (I : Ideal A)
    (hI : IsOpen (I : Set A)) (q : PrimeSpectrum (A ⧸ I)) :
    IsOpen ((PrimeSpectrum.comap (Ideal.Quotient.mk I) q).asIdeal : Set A) := sorry

/-- The open prime obtained by pulling a quotient prime back along the quotient map. -/
def ofQuotient [IsTopologicalRing A] (I : Ideal A) (hI : IsOpen (I : Set A))
    (q : PrimeSpectrum (A ⧸ I)) : OpenPrime A :=
  ⟨PrimeSpectrum.comap (Ideal.Quotient.mk I) q, isOpen_comap_quotient I hI q⟩

/-- The quotient-prime pullback is continuous for the subspace topology. -/
theorem continuous_ofQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : IsOpen (I : Set A)) : Continuous (ofQuotient I hI) := sorry

/-- The quotient-prime pullback bundled as a continuous map. -/
def ofQuotientContinuous [IsTopologicalRing A] (I : Ideal A) (hI : IsOpen (I : Set A)) :
    C(PrimeSpectrum (A ⧸ I), OpenPrime A) :=
  ⟨ofQuotient I hI, continuous_ofQuotient I hI⟩

/-- Pullback of an open prime along a continuous ring homomorphism. -/
def comap {B : Type u} [CommRing B] [TopologicalSpace B] (φ : A →+* B)
    (hφ : Continuous φ) (p : OpenPrime B) : OpenPrime A :=
  ⟨PrimeSpectrum.comap φ p.toPrimeSpectrum,
    Ideal.coe_comap φ p.asIdeal ▸ p.property.preimage hφ⟩

/-- Pullback of open primes is continuous. -/
theorem continuous_comap {B : Type u} [CommRing B] [TopologicalSpace B] (φ : A →+* B)
    (hφ : Continuous φ) : Continuous (comap φ hφ) := sorry

/-- The image of an open prime modulo an ideal of definition is prime. -/
theorem isPrime_map_quotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (p : OpenPrime A) :
    (Ideal.map (Ideal.Quotient.mk I) p.asIdeal).IsPrime := sorry

/-- The quotient prime obtained by taking the image of an open prime ideal. -/
def toQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (p : OpenPrime A) :
    PrimeSpectrum (A ⧸ I) :=
  ⟨Ideal.map (Ideal.Quotient.mk I) p.asIdeal, isPrime_map_quotient I hI p⟩

/-- Quotient image and pullback are continuous inverse maps for an ideal of definition. -/
theorem homeomorphQuotient_laws [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    Function.LeftInverse (ofQuotient I hI.1) (toQuotient I hI) ∧
      Function.RightInverse (ofQuotient I hI.1) (toQuotient I hI) ∧
      Continuous (toQuotient I hI) ∧ Continuous (ofQuotient I hI.1) := sorry

/-- Open primes are homeomorphic to the spectrum of the quotient by an ideal of definition. -/
def homeomorphQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    OpenPrime A ≃ₜ PrimeSpectrum (A ⧸ I) where
  toFun := toQuotient I hI
  invFun := ofQuotient I hI.1
  left_inv := (homeomorphQuotient_laws I hI).1
  right_inv := (homeomorphQuotient_laws I hI).2.1
  continuous_toFun := (homeomorphQuotient_laws I hI).2.2.1
  continuous_invFun := (homeomorphQuotient_laws I hI).2.2.2

/-- The continuous inverse of the quotient-spectrum homeomorphism. -/
def homeomorphQuotientInv [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    C(PrimeSpectrum (A ⧸ I), OpenPrime A) :=
  ⟨(homeomorphQuotient I hI).symm, (homeomorphQuotient I hI).continuous_invFun⟩

/-- The continuous inverse has the same point map as the inverse homeomorphism. -/
theorem homeomorphQuotientInv_apply [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (q : PrimeSpectrum (A ⧸ I)) :
    homeomorphQuotientInv I hI q = (homeomorphQuotient I hI).symm q := sorry

end OpenPrime

end AlgebraicGeometry.FormalSpectrum
