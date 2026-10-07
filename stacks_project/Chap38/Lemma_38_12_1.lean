module

public import ReasLib.RingTheory.Flatness.FiberBasis.AtPrime
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u v z

/- Lemma 38.12.1 (1): for a prime `q` of a finitely presented flat `R`-algebra `S` lying over
`p`, and the extended prime `P = pS`, a finitely presented `S`-module admits a finite free map
that is an isomorphism on the fibre at `P`. -/
@[stacks 05IA] #check
  (Module.exists_fiberBasisMap_of_liesOver :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
      [Algebra.FinitePresentation R S] [Module.Flat R S]
      [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
      {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
      [Module.FinitePresentation S N]
      (p : PrimeSpectrum R) (P q : PrimeSpectrum S),
      P.asIdeal = Ideal.map (algebraMap R S) p.asIdeal →
      PrimeSpectrum.comap (algebraMap R S) q = p →
      ∃ n : ℕ, ∃ alpha : (Fin n → S) →ₗ[S] N, alpha.IsFiberBijectiveAt P)

/- Lemma 38.12.1 (2): for any finite free map inducing an isomorphism on the fibre at the
extended prime `P = pS`, flatness of `N` at `q` is equivalent to the principal-neighbourhood,
base-prime, injective, and local-isomorphism criteria, each with the stated flat cokernel. -/
@[stacks 05IA] #check
  (Module.fiberBasisMap_flatAtPrime_tfae_of_liesOver :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
      [Algebra.FinitePresentation R S] [Module.Flat R S]
      [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
      {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
      [Module.FinitePresentation S N]
      (p : PrimeSpectrum R) (P q : PrimeSpectrum S),
      P.asIdeal = Ideal.map (algebraMap R S) p.asIdeal →
      PrimeSpectrum.comap (algebraMap R S) q = p →
      ∀ (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N), alpha.IsFiberBijectiveAt P →
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
      ])
