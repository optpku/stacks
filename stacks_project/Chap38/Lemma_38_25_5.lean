/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.RestrictScalars

@[expose] public section

universe u v w x

/- Lemma 38.25.5 (1): an essentially finite type local homomorphism carries a finite
`B`-module map with injective closed fiber and `A`-flat target to an `A`-universally
injective map after restriction of scalars. -/
@[stacks 0AT4] #check
  (LinearMap.ClosedFiber.universallyInjective_restrictScalars :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
      [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[B] M),
      Function.Injective
          ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
        LinearMap.UniversallyInjective.{u, x, w, max u x w} (u.restrictScalars A))

/- Lemma 38.25.5 (2): under the same closed-fiber criterion, the finite `B`-module
`N` is finitely presented over `B`. -/
@[stacks 0AT4] #check
  (LinearMap.ClosedFiber.finitePresentation_domain_restrictScalars :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
      [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[B] M),
      Function.Injective
          ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
        Module.FinitePresentation B N)

/- Lemma 38.25.5 (3): under the same closed-fiber criterion, the finite `B`-module
`N` is flat over `A`. -/
@[stacks 0AT4] #check
  (LinearMap.ClosedFiber.flat_domain_restrictScalars :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      {M : Type w} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
      [Module.Flat A M]
      {N : Type x} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
      [Module.Finite B N] (u : N →ₗ[B] M),
      Function.Injective
          ((u.restrictScalars A).quotientMapByIdeal (IsLocalRing.maximalIdeal A)) →
        Module.Flat A N)
