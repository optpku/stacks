/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.IntegerValuation
import StacksCheckRecall

@[expose] public section

open Polynomial

universe u

/- Exercise 111.1.8 (1): if `f`, `g`, and `f + g` are nonzero and `ν f ≠ ν g`,
then `ν (f + g) = min (ν f) (ν g)`. -/
@[stacks 02CN] #check (Polynomial.map_add_eq_min :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν] {f g : k[X]},
    f ≠ 0 → g ≠ 0 → f + g ≠ 0 → ν f ≠ ν g → ν (f + g) = min (ν f) (ν g))

/- Exercise 111.1.8 (2): if `f ≠ 0`, then `ν f` is at least the infimum of
`i * ν X` over those degrees `i` in the support of `f`. -/
@[stacks 02CN] #check (Polynomial.gauss_le :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν]
    {f : k[X]} (hf : f ≠ 0), Polynomial.gaussMin ν hf ≤ ν f)

#check (Polynomial.gauss_eq_iff :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν]
    {f : k[X]} (hf : f ≠ 0), ν f = Polynomial.gaussMin ν hf ↔ ν X ≠ 0 ∨ ν f = 0)

/- Exercise 111.1.8 (3): if `ν` attains a negative value, then
`ν g = scaledNegDegree (-(ν X)).toNat g` for every nonzero `g`. -/
@[stacks 02CN] #check (Polynomial.eq_scaledNegDegree_of_exists_neg :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν],
    (∃ f : k[X], f ≠ 0 ∧ ν f < 0) → ∀ {g : k[X]},
      g ≠ 0 → ν g = Polynomial.scaledNegDegree (-(ν X)).toNat g)

#check (Polynomial.exists_neg_iff_neg_X :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν],
    (∃ f : k[X], f ≠ 0 ∧ ν f < 0) ↔ ν X < 0)

/- Exercise 111.1.8 (4): if `ν X ≥ 0`, then `{f | f = 0 ∨ 0 < ν f}` is a prime
ideal of `k[X]`. -/
@[stacks 02CN] #check (Polynomial.strictPosIdeal.isPrime :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν]
    (hX : 0 ≤ ν X), (Polynomial.strictPosIdeal ν hX).IsPrime)

#check (Polynomial.mem_strictPosIdeal_iff :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν]
    (hX : 0 ≤ ν X) {f : k[X]}, f ∈ Polynomial.strictPosIdeal ν hX ↔ f = 0 ∨ 0 < ν f)

#check (Polynomial.nonneg_of_nonneg_X :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν],
    0 ≤ ν X → ∀ {f : k[X]}, f ≠ 0 → 0 ≤ ν f)

/- Exercise 111.1.8 (5): every such `ν` is either a scaled negative degree
(including the zero map at `n = 0`) or a strictly positive scaled prime
multiplicity. -/
@[stacks 02CN] #check (Polynomial.eq_scaledNegDegree_or_scaledMultiplicity :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ) [Polynomial.IsIntegerValuation ν],
    (∃ n : ℕ, ∀ f : k[X], f ≠ 0 → ν f = Polynomial.scaledNegDegree n f) ∨
      ∃ p : k[X], ∃ n : ℕ, Prime p ∧ 0 < n ∧
        ∀ f : k[X], f ≠ 0 → ν f = Polynomial.scaledMultiplicity p n f)

#check (Polynomial.instIsIntegerValuation_trivialValuation :
  ∀ {k : Type u} [Field k], Polynomial.IsIntegerValuation (Polynomial.trivialValuation : k[X] → ℤ))

#check (Polynomial.instIsIntegerValuation_scaledNegDegree :
  ∀ {k : Type u} [Field k] (n : ℕ),
    Polynomial.IsIntegerValuation (Polynomial.scaledNegDegree n : k[X] → ℤ))

#check (Polynomial.instIsIntegerValuation_scaledMultiplicity :
  ∀ {k : Type u} [Field k] (p : k[X]) (n : ℕ) [Fact (Prime p)],
    Polynomial.IsIntegerValuation (Polynomial.scaledMultiplicity p n))

#check (Polynomial.scaledNegDegree_scale_unique :
  ∀ {k : Type u} [Field k] {n m : ℕ},
    (∀ f : k[X], f ≠ 0 → Polynomial.scaledNegDegree n f = Polynomial.scaledNegDegree m f) → n = m)

#check (Polynomial.scaledMultiplicity_scale_unique :
  ∀ {k : Type u} [Field k] {p q : k[X]} {n m : ℕ},
    Prime p → Prime q → 0 < n → 0 < m →
      (∀ f : k[X], f ≠ 0 → Polynomial.scaledMultiplicity p n f = Polynomial.scaledMultiplicity q m f) →
      n = m)

#check (Polynomial.scaledMultiplicity_associated :
  ∀ {k : Type u} [Field k] {p q : k[X]} {n m : ℕ},
    Prime p → Prime q → 0 < n → 0 < m →
      (∀ f : k[X], f ≠ 0 → Polynomial.scaledMultiplicity p n f = Polynomial.scaledMultiplicity q m f) →
      Associated p q)

#check (Polynomial.isIntegerValuation_iff :
  ∀ {k : Type u} [Field k] (ν : k[X] → ℤ),
    Polynomial.IsIntegerValuation ν ↔
      (∀ ⦃f g : k[X]⦄, f ≠ 0 → g ≠ 0 → ν (f * g) = ν f + ν g) ∧
        (∀ ⦃f g : k[X]⦄, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (ν f) (ν g) ≤ ν (f + g)) ∧
          (∀ ⦃c : k⦄, c ≠ 0 → ν (C c) = 0))
