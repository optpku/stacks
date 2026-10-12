/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Henselian

@[expose] public section

universe u v w x

/- Lemma 38.25.4 (1): in Situation 38.25.1, if `A` is Henselian, then `u` is
universally injective as an `A`-linear map. -/
@[stacks 0AT3] #check
  (LinearMap.ClosedFiber.universallyInjective_of_henselian :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [HenselianLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M),
      Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
        LinearMap.UniversallyInjective.{u, x, w, max u x w} u)

/- Lemma 38.25.4 (2): in Situation 38.25.1, if `A` is Henselian, then `N` is
flat over `A`. -/
@[stacks 0AT3] #check
  (LinearMap.ClosedFiber.flat_domain_of_henselian :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [HenselianLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M),
      Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
        Module.Flat A N)

/- Lemma 38.25.4 (3): in Situation 38.25.1, if `A` is Henselian, then `N` is
finitely presented over `B`. -/
@[stacks 0AT3] #check
  (LinearMap.ClosedFiber.finitePresentation_domain_of_henselian :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [HenselianLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module A M] [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[A] M),
      Function.Injective (u.quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
        Module.FinitePresentation B N)
