/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.AssociatedPrime
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

/- Lemma 49.2.8: for a quasi-finite homomorphism `A → B` of Noetherian rings, the
associated primes of the relative dualizing `B`-module are exactly the primes of `B`
lying over associated primes of `A`. -/
@[stacks 0BVD] #check
  (Algebra.RelativeDualizingModule.associatedPrimes_eq_liesOver :
    ∀ (A : Type u) (B' B : Type v)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))),
      { q : PrimeSpectrum B |
          q.asIdeal ∈ associatedPrimesOfModule B
            (Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open) } =
        { q : PrimeSpectrum B |
          q.asIdeal.under A ∈ associatedPrimesOfModule A A })
