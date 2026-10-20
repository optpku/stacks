/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Relative
public import ReasLib.RingTheory.Localization.ClosedFiber.BaseChange
public import ReasLib.LinearAlgebra.UniversallyInjective.Localization.AtPrime

/-!
# Universal injectivity from relative associated-prime coverage

This file gives a criterion for universal injectivity of a flat base-change map in terms of
the relative associated primes of a module.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x z

namespace relativeAssassin

/-- Let `R → S` be a finitely presented map of rings, let `N` be a finitely presented
`S`-module that is flat over `R`, and let `S → S'` be flat. If the image of
`Spec(S') → Spec(S)` contains `relativeAssassin R S N`, then the canonical map
`N → S' ⊗[S] N` is universally injective over `R`. -/
@[stacks 05DH]
theorem universallyInjective_baseChange
    {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
    [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N]
    [Module.Flat R N] [Module.Flat S S']
    (h_range : relativeAssassin R S N ⊆
      Set.range (PrimeSpectrum.comap (algebraMap S S'))) :
    LinearMap.UniversallyInjective.{u, x, max w x, z}
      ((TensorProduct.mk S S' N 1).restrictScalars R) := sorry

end relativeAssassin
