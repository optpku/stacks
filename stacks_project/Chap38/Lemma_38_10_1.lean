/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.FiberBasis
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u v

/- Lemma 38.10.1 (1): over a local ring, a finite module over a finitely presented flat
algebra with geometrically integral fibres admits a finite free map inducing an isomorphism
on the fibre over the extended maximal ideal. -/
@[stacks 05I3] #check (Module.exists_fiberBasisMap :
  ∀ {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (p q : PrimeSpectrum S)
    (hp : p.asIdeal = Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
    (hq : PrimeSpectrum.comap (algebraMap R S) q = IsLocalRing.closedPoint R),
    ∃ r : ℕ, ∃ α : (Fin r → S) →ₗ[S] N, α.IsFiberBijectiveAt p)

/- Lemma 38.10.1 (2): for a finite free map inducing an isomorphism on the fibre over the
extended maximal ideal, flatness at a prime over the maximal ideal is equivalent to the four
universal-injectivity, injectivity, and localized map criteria with flat localized cokernel. -/
@[stacks 05I3] #check (Module.fiberBasisMap_flatAtPrime_tfae :
  ∀ {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    {N : Type v} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N]
    (p q : PrimeSpectrum S)
    (hp : p.asIdeal = Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
    (hq : PrimeSpectrum.comap (algebraMap R S) q = IsLocalRing.closedPoint R)
    (r : ℕ) (α : (Fin r → S) →ₗ[S] N) (hα : α.IsFiberBijectiveAt p),
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
    ])
