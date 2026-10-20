module

import StacksCheckRecall
import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.PolynomialLocalization

@[expose] public section

universe u v w x z

/- Lemma 38.25.3 (1): universal injectivity in Situation 38.25.1 over a fixed
local ring follows from the cases in which the target algebra is a localization
of a finite-variable polynomial algebra and the source module is finitely presented. -/
@[stacks 0AT2] #check
  (LinearMap.ClosedFiber.universallyInjective_of_polynomialLocalization :
    ∀ (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀],
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          LinearMap.UniversallyInjective.{u, u, w, max u v w x z} f) →
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.Flat A₀ N) →
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.FinitePresentation C N) →
      ∀ {B : Type v} [CommRing B] [Algebra A₀ B]
        [IsLocalRing B] [IsLocalHom (algebraMap A₀ B)] [Algebra.EssFiniteType A₀ B]
        {M : Type w} [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        {N : Type x} [AddCommGroup N] [Module B N] [Module A₀ N]
        [IsScalarTower A₀ B N] [Module.Finite B N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          LinearMap.UniversallyInjective.{u, x, w, max u v w x z} f)

/- Lemma 38.25.3 (2): flatness in Situation 38.25.1 over a fixed local ring
follows from the cases in which the target algebra is a localization of a
finite-variable polynomial algebra and the source module is finitely presented. -/
@[stacks 0AT2] #check
  (LinearMap.ClosedFiber.flat_domain_of_polynomialLocalization :
    ∀ (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀],
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          LinearMap.UniversallyInjective.{u, u, w, max u v w x z} f) →
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.Flat A₀ N) →
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.FinitePresentation C N) →
      ∀ {B : Type v} [CommRing B] [Algebra A₀ B]
        [IsLocalRing B] [IsLocalHom (algebraMap A₀ B)] [Algebra.EssFiniteType A₀ B]
        {M : Type w} [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        {N : Type x} [AddCommGroup N] [Module B N] [Module A₀ N]
        [IsScalarTower A₀ B N] [Module.Finite B N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.Flat A₀ N)

/- Lemma 38.25.3 (3): finite presentation in Situation 38.25.1 over a fixed
local ring follows from the cases in which the target algebra is a localization
of a finite-variable polynomial algebra and the source module is finitely presented. -/
@[stacks 0AT2] #check
  (LinearMap.ClosedFiber.finitePresentation_domain_of_polynomialLocalization :
    ∀ (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀],
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          LinearMap.UniversallyInjective.{u, u, w, max u v w x z} f) →
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.Flat A₀ N) →
      (∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.FinitePresentation C N) →
      ∀ {B : Type v} [CommRing B] [Algebra A₀ B]
        [IsLocalRing B] [IsLocalHom (algebraMap A₀ B)] [Algebra.EssFiniteType A₀ B]
        {M : Type w} [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        {N : Type x} [AddCommGroup N] [Module B N] [Module A₀ N]
        [IsScalarTower A₀ B N] [Module.Finite B N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.FinitePresentation B N)
