/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ZariskisMainTheorem
public import ReasLib.RingTheory.NoetherNormalization
public import ReasLib.RingTheory.Ideal.ChineseRemainder
public import ReasLib.RingTheory.Ideal.GoingUp.Finite
import StacksCheckRecall

@[expose] public section

universe u v

open Function
open scoped BigOperators

/- Exercise 111.55.2 (Results) (1): Zariski's Main Theorem. -/
@[stacks 07DG] #check
  (Algebra.QuasiFiniteAt.exists_integral_notMem_forall_isIntegral_pow_mul :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Algebra.FiniteType R S] (prime : Ideal S) [prime.IsPrime]
      [Algebra.QuasiFiniteAt R prime],
      ∃ element : S, element ∉ prime ∧ IsIntegral R element ∧
        ∀ value : S, ∃ exponent : ℕ, IsIntegral R (element ^ exponent * value))

/- Exercise 111.55.2 (Results) (2): Noether normalization. -/
@[stacks 07DG] #check
  (Algebra.exists_injective_finite_mvPolynomial :
    ∀ (field ring : Type u) [Field field] [CommRing ring] [Nontrivial ring]
      [Algebra field ring] [Algebra.FiniteType field ring],
      ∃ count : ℕ, ∃ embedding : MvPolynomial (Fin count) field →ₐ[field] ring,
        Function.Injective embedding ∧ embedding.Finite)

/- Exercise 111.55.2 (Results) (3): Chinese remainder theorem. -/
@[stacks 07DG] #check
  (Ideal.ChineseRemainder.quotientProdEquiv :
    ∀ {R : Type u} {ι : Type v} [CommRing R] [Fintype ι] (ideals : ι → Ideal R),
      Pairwise (IsCoprime on ideals) → (R ⧸ ∏ i, ideals i) ≃+* ∀ i, R ⧸ ideals i)

/- Exercise 111.55.2 (Results) (4): going up for finite ring maps. -/
@[stacks 07DG] #check
  (Ideal.exists_prime_over_of_finite :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Module.Finite R S] (basePrime : Ideal R) [basePrime.IsPrime]
      (prime : Ideal S) [prime.IsPrime],
      prime.comap (algebraMap R S) ≤ basePrime →
        ∃ overPrime ≥ prime, overPrime.IsPrime ∧
          overPrime.comap (algebraMap R S) = basePrime)
