module

public import Mathlib.Tactic.TFAE
public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
public import ReasLib.RingTheory.Flat.Projective.GeometricallyIntegral
public import ReasLib.RingTheory.Module.Support.LinearMap

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u v

namespace Module

/-- Over a local ring, a finite module over a finitely presented flat algebra with
geometrically integral fibers admits a finite free map inducing an isomorphism on
the fiber over the extended maximal ideal. -/
theorem exists_fiberBasisMap
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (p q : PrimeSpectrum S)
    (hp : p.asIdeal = Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
    (hq : PrimeSpectrum.comap (algebraMap R S) q = IsLocalRing.closedPoint R) :
    ∃ r : ℕ, ∃ α : (Fin r → S) →ₗ[S] N, α.IsFiberBijectiveAt p := sorry

/-- For a finite free map inducing an isomorphism on the fiber over the extended
maximal ideal, flatness at a prime over the maximal ideal is equivalent to four
injectivity criteria together with flatness of the localized cokernel. -/
theorem fiberBasisMap_flatAtPrime_tfae
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (p q : PrimeSpectrum S)
    (hp : p.asIdeal = Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
    (hq : PrimeSpectrum.comap (algebraMap R S) q = IsLocalRing.closedPoint R)
    (r : ℕ) (α : (Fin r → S) →ₗ[S] N) (hα : α.IsFiberBijectiveAt p) :
    List.TFAE [
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal N),
      LinearMap.UniversallyInjective (α.restrictScalars R) ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ α.range)),
      Function.Injective α ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ α.range)),
      α.IsBijectiveAt p ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ α.range)),
      α.IsInjectiveAt q ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ α.range))
    ] := sorry

end Module
