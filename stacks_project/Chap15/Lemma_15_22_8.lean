/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.TorsionFree
import StacksCheckRecall

/-!
# Lemma 15.22.8

The reusable five-way characterization is owned by
`Module.IsTorsionFree.tfae_associatedPrimes_support_serreS1`.

@stack 0AUV
-/

@[expose] public section

universe u v

open Module

@[stacks 0AUV "Lemma 15.22.8"]
#check fun {R : Type u} {M : Type v}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] ↦
  (Module.IsTorsionFree.tfae_associatedPrimes_support_serreS1 (R := R) (M := M) :
    List.TFAE
      [ IsTorsionFree R M,
        ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f,
        associatedPrimes R M = {⊥},
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ SerreConditionS R M 1,
        (⊥ : PrimeSpectrum R) ∈ support R M ∧ embeddedAssociatedPrimes R M = ∅ ])
