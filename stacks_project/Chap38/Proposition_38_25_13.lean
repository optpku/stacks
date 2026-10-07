module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.EssFiniteType
import StacksCheckRecall

@[expose] public section

universe u v w x

/- Proposition 38.25.13 (1): a finite module map into a flat module that is injective
on the closed fiber is universally injective when the local algebra is essentially of finite type. -/
@[stacks 05U9] #check
  (LinearMap.ClosedFiber.universallyInjective_of_essFiniteType :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M)
      (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))),
      LinearMap.UniversallyInjective.{u, x, w, max u x w} u)

/- Proposition 38.25.13 (2): under the closed-fiber injectivity hypotheses, the finite
`B`-module `N` is finitely presented over `B`. -/
@[stacks 05U9] #check
  (LinearMap.ClosedFiber.finitePresentation_domain_of_essFiniteType :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M)
      (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))),
      Module.FinitePresentation B N)

/- Proposition 38.25.13 (3): under the closed-fiber injectivity hypotheses, the finite
`B`-module `N` is flat over `A`. -/
@[stacks 05U9] #check
  (LinearMap.ClosedFiber.flat_domain_of_essFiniteType :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M)
      (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))),
      Module.Flat A N)
