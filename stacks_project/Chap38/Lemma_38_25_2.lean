/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.EssFiniteType
import StacksCheckRecall

@[expose] public section

universe u v w x

/- Lemma 38.25.2 (1): in Situation 38.25.1, if `A` is Noetherian, then `u` is
universally injective as an `A`-linear map. -/
@[stacks 0AT1] #check
  (LinearMap.ClosedFiber.universallyInjective_of_noetherian :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B] [IsNoetherianRing A]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M)
      (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))),
      LinearMap.UniversallyInjective.{u, x, w, max u x w} u)

/- Lemma 38.25.2 (2): in Situation 38.25.1, if `A` is Noetherian, then `N` is
flat over `A`. -/
@[stacks 0AT1] #check
  (LinearMap.ClosedFiber.flat_domain_of_noetherian :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B] [IsNoetherianRing A]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M)
      (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))),
      Module.Flat A N)

/- Lemma 38.25.2 (3): in Situation 38.25.1, if `A` is Noetherian, then `N` is
finitely presented over `B`. -/
@[stacks 0AT1] #check
  (LinearMap.ClosedFiber.finitePresentation_domain_of_noetherian :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B] [IsNoetherianRing A]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M)
      (hbar : Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A))),
      Module.FinitePresentation B N)
