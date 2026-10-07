module

public import ReasLib.LinearAlgebra.UniversallyInjective.Localization.Relative
public import ReasLib.RingTheory.Flatness.FiberBasis

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u v z

namespace Module

/-- For a prime `q` of a finitely presented flat `R`-algebra `S` lying over `p`, and the
extended prime `P = pS`, a finitely presented `S`-module admits a finite free map inducing an
isomorphism on the fibre at `P`. -/
theorem exists_fiberBasisMap_of_liesOver
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N]
    (p : PrimeSpectrum R) (P q : PrimeSpectrum S)
    (hP : P.asIdeal = Ideal.map (algebraMap R S) p.asIdeal)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    ∃ n : ℕ, ∃ alpha : (Fin n → S) →ₗ[S] N, alpha.IsFiberBijectiveAt P := sorry

/-- For any finite free map inducing an isomorphism on the fibre at the extended prime `P = pS`,
flatness of `N` at a prime `q` over `p` is equivalent to the principal-neighbourhood,
base-prime, extended-prime, and prime-local injectivity criteria, with the stated flat localized
cokernel. -/
theorem fiberBasisMap_flatAtPrime_tfae_of_liesOver
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N]
    (p : PrimeSpectrum R) (P q : PrimeSpectrum S)
    (hP : P.asIdeal = Ideal.map (algebraMap R S) p.asIdeal)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p)
    (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N) (h_alpha : alpha.IsFiberBijectiveAt P) :
    List.TFAE [
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal N),
      ∃ f : R, f ∉ p.asIdeal ∧
        LinearMap.UniversallyInjective.awayOverBase.{u, u, u, v, z} alpha f ∧
        ∃ g : S, g ∉ q.asIdeal ∧
          Module.Flat R (LocalizedModule.Away g (N ⧸ alpha.range)),
      LinearMap.UniversallyInjective.atBasePrime.{u, u, u, v, z} alpha p ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ alpha.range)),
      Function.Injective
          (LocalizedModule.map
            (Submonoid.map (algebraMap R S) p.asIdeal.primeCompl) alpha) ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ alpha.range)),
      alpha.IsBijectiveAt P ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ alpha.range)),
      alpha.IsInjectiveAt q ∧
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal (N ⧸ alpha.range))
    ] := sorry

end Module
