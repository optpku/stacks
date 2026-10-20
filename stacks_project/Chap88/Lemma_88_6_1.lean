/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.Perturbation
import StacksCheckRecall

/-!
# Nearby presentations of rig-smooth completed quotients

If `B` is a rig-smooth quotient of `P = A[x_ι]^∧` presented by an exact
generator-relation complex, then any nearby complex congruent modulo a
sufficiently high power of `I P` presents an isomorphic `A`-algebra.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic

/- Lemma 88.6.1: Let `I` be an ideal of a Noetherian ring `A`, and write
`P` for `polynomialCompletion A I ι`. Given an exact resolution
`P^τ ⟶ P^κ ⟶ P → B → 0` of a quotient of `P` by generators `g` and
relations `K`, assume `B` is rig-smooth over `(A, I)`. Then there exists
an integer `n` such that for any complex `P^τ ⟶ P^κ ⟶ P` given by `g'`
and `K'` with `g i - g' i ∈ I ^ n P` and `(K - K') i j ∈ I ^ n P`, there
is an `A`-algebra isomorphism `B ≃ₐ[A] P ⧸ Ideal.span (Set.range g')`. -/
@[stacks 0GAR]
#check (Algebra.NaiveCotangent.Adic.exists_algEquiv_of_congr_mod_pow :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      {ι κ τ : Type u} [Fintype ι] [Fintype κ] [Fintype τ]
      (g : κ → polynomialCompletion A I ι)
    (K : Matrix κ τ (polynomialCompletion A I ι))
    (hres : Function.Exact (Matrix.mulVecLin K)
      (Fintype.linearCombination (polynomialCompletion A I ι) g))
    [Algebra.RigSmooth I
      (polynomialCompletion A I ι ⧸ Ideal.span (Set.range g))],
    ∃ n : ℕ, ∀ (g' : κ → polynomialCompletion A I ι)
        (K' : Matrix κ τ (polynomialCompletion A I ι)),
      (∀ i, g i - g' i ∈
        (I.map (algebraMap A (polynomialCompletion A I ι))) ^ n) →
      (∀ i j, (K - K') i j ∈
        (I.map (algebraMap A (polynomialCompletion A I ι))) ^ n) →
      ((Fintype.linearCombination (polynomialCompletion A I ι) g').comp
          (Matrix.mulVecLin K') = 0) →
      Nonempty
        ((polynomialCompletion A I ι ⧸ Ideal.span (Set.range g)) ≃ₐ[A]
          (polynomialCompletion A I ι ⧸ Ideal.span (Set.range g'))))
