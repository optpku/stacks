/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Fiber
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

/- Lemma 38.13.2: for a finitely presented ring map `R → S` and a finitely presented
`S`-module `N` that is flat over `R`, a prime `q` over `p` is weakly associated to
`N ⊗[R] M` exactly when `p` is weakly associated to `M` and the canonical fiber prime
is associated to the canonical fiber module. -/
@[stacks 05IG]
#check
  (weaklyAssociatedPrimes.Fiber.mem_tensorProduct_iff :
    ∀ {R : Type u} {S : Type v} {M : Type w} {N : Type x}
      [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
      [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
      [Module.FinitePresentation S N] [Module.Flat R N]
      (p : PrimeSpectrum R) (q : PrimeSpectrum S)
      (hq : PrimeSpectrum.comap (algebraMap R S) q = p),
      q.asIdeal ∈ weaklyAssociatedPrimes S (N ⊗[R] M) ↔
        p.asIdeal ∈ weaklyAssociatedPrimes R M ∧
          (PrimeSpectrum.fiberPrime p q hq).asIdeal ∈
            associatedPrimesOfModule (p.asIdeal.Fiber S)
              ((p.asIdeal.Fiber S) ⊗[S] N))
