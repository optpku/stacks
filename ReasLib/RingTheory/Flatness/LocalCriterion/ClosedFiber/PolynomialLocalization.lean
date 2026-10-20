module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
public import ReasLib.Algebra.Module.FinitePresentation.Approximation
public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.LinearAlgebra.UniversallyInjective.Operations
public import ReasLib.RingTheory.EssentialFiniteness.LocalPresentation

/-!
# Reduction to polynomial localizations in the closed-fiber criterion

The closed-fiber conclusions for a local essentially finite-type algebra reduce
to finitely presented modules over localizations of finite-variable polynomial
algebras.
-/

@[expose] public section

universe u v w x z

namespace LinearMap.ClosedFiber

/-- Universal injectivity in the closed-fiber situation reduces to the case of
finitely presented modules over localizations of finite-variable polynomial
algebras. -/
theorem universallyInjective_of_polynomialLocalization
    (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀]
    (h_universallyInjective :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          LinearMap.UniversallyInjective.{u, u, w, max u v w x z} f)
    (h_flat :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.Flat A₀ N)
    (h_finitePresentation :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.FinitePresentation C N)
    {B : Type v} [CommRing B] [Algebra A₀ B]
    [IsLocalRing B] [IsLocalHom (algebraMap A₀ B)] [Algebra.EssFiniteType A₀ B]
    {M : Type w} [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A₀ N]
    [IsScalarTower A₀ B N] [Module.Finite B N]
    (f : N →ₗ[A₀] M)
    (hbar : Function.Injective
      (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀))) :
    LinearMap.UniversallyInjective.{u, x, w, max u v w x z} f := sorry

/-- Flatness of the domain in the closed-fiber situation reduces to the case
of finitely presented modules over localizations of finite-variable polynomial
algebras. -/
theorem flat_domain_of_polynomialLocalization
    (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀]
    (h_universallyInjective :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          LinearMap.UniversallyInjective.{u, u, w, max u v w x z} f)
    (h_flat :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.Flat A₀ N)
    (h_finitePresentation :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.FinitePresentation C N)
    {B : Type v} [CommRing B] [Algebra A₀ B]
    [IsLocalRing B] [IsLocalHom (algebraMap A₀ B)] [Algebra.EssFiniteType A₀ B]
    {M : Type w} [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A₀ N]
    [IsScalarTower A₀ B N] [Module.Finite B N]
    (f : N →ₗ[A₀] M)
    (hbar : Function.Injective
      (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀))) :
    Module.Flat A₀ N := sorry

/-- Finite presentation of the domain in the closed-fiber situation reduces to
the case of finitely presented modules over localizations of finite-variable
polynomial algebras. -/
theorem finitePresentation_domain_of_polynomialLocalization
    (A₀ : Type u) [CommRing A₀] [IsLocalRing A₀]
    (h_universallyInjective :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          LinearMap.UniversallyInjective.{u, u, w, max u v w x z} f)
    (h_flat :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.Flat A₀ N)
    (h_finitePresentation :
      ∀ (n : ℕ) (C : Type u) (S : Submonoid (MvPolynomial (Fin n) A₀))
        [CommRing C] [Algebra A₀ C] [Algebra (MvPolynomial (Fin n) A₀) C]
        [IsScalarTower A₀ (MvPolynomial (Fin n) A₀) C] [IsLocalization S C]
        [IsLocalRing C] [IsLocalHom (algebraMap A₀ C)] [Algebra.EssFiniteType A₀ C]
        (M : Type w) [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
        (N : Type u) [AddCommGroup N] [Module C N] [Module A₀ N]
        [IsScalarTower A₀ C N] [Module.Finite C N] [Module.FinitePresentation C N]
        (f : N →ₗ[A₀] M),
        Function.Injective (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀)) →
          Module.FinitePresentation C N)
    {B : Type v} [CommRing B] [Algebra A₀ B]
    [IsLocalRing B] [IsLocalHom (algebraMap A₀ B)] [Algebra.EssFiniteType A₀ B]
    {M : Type w} [AddCommGroup M] [Module A₀ M] [Module.Flat A₀ M]
    {N : Type x} [AddCommGroup N] [Module B N] [Module A₀ N]
    [IsScalarTower A₀ B N] [Module.Finite B N]
    (f : N →ₗ[A₀] M)
    (hbar : Function.Injective
      (f.quotientMapByIdeal (IsLocalRing.maximalIdeal A₀))) :
    Module.FinitePresentation B N := sorry

end LinearMap.ClosedFiber
