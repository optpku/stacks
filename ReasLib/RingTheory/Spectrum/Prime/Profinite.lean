module

public import ReasLib.RingTheory.Spectrum.Prime.BasicOpen
public import ReasLib.RingTheory.Spectrum.Prime.Irreducible
public import ReasLib.Topology.ConstructibleTopology.Profinite

/-!
# Profinite prime spectra

@stack 04MG

This leaf specializes the canonical profinite criteria for spectral spaces to
prime spectra and adds the principal-basic-open formulation used in
commutative algebra.
-/

@[expose] public section

open Set TopologicalSpace

universe u

namespace PrimeSpectrum

/-- Lemma 10.26.5: the standard separation, specialization, irreducible-component, and
principal-basic-open criteria for a prime spectrum to be profinite are equivalent. -/
@[stacks 04MG]
theorem profinite_criteria (R : Type u) [CommRing R] :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (PrimeSpectrum R ≃ₜ P)
      , T2Space (PrimeSpectrum R)
      , TotallyDisconnectedSpace (PrimeSpectrum R)
      , ∀ U : Set (PrimeSpectrum R), IsOpen U → IsCompact U → IsClosed U
      , ∀ ⦃p q : PrimeSpectrum R⦄, p ⤳ q → p = q
      , ∀ p : PrimeSpectrum R, IsClosed ({p} : Set (PrimeSpectrum R))
      , ∀ p : PrimeSpectrum R, IsGenericPoint p (irreducibleComponent p)
      , ∀ f : R, IsClosed ((basicOpen f : Set (PrimeSpectrum R)))
      ] := sorry

end PrimeSpectrum
