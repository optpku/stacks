/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne.Regular
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing

/- Exercise 111.28.5 (1): if `A` is a regular local ring of dimension 1 and
`x ∈ maximalIdeal A` has nonzero class in `(maximalIdeal A) / (maximalIdeal A) ^ 2`,
then every nonzero `y ∈ maximalIdeal A` may be written as `y = u * x ^ n` for some
unit `u : Aˣ` and some `n : ℕ`. -/
@[stacks 02EJ] #check (IsRegularLocalRing.exists_unit_mul_pow_of_mem_maximalIdeal :
    ∀ {A : Type u} [CommRing A] [IsRegularLocalRing A], ringKrullDim A = 1 →
      ∀ {x : A}, x ∈ maximalIdeal A → x ∉ maximalIdeal A ^ 2 →
        ∀ {y : A}, y ∈ maximalIdeal A → y ≠ 0 →
          ∃ n : ℕ, ∃ u : Aˣ, y = u * x ^ n)

/- Exercise 111.28.5 (2): if `A` is a regular local ring of dimension 1 and
`x ∈ maximalIdeal A` has nonzero class in `(maximalIdeal A) / (maximalIdeal A) ^ 2`,
then `x` is a nonzerodivisor on `A`. -/
@[stacks 02EJ] #check (IsRegularLocalRing.isSMulRegular_of_not_mem_sq :
    ∀ {A : Type u} [CommRing A] [IsRegularLocalRing A], ringKrullDim A = 1 →
      ∀ {x : A}, x ∈ maximalIdeal A → x ∉ maximalIdeal A ^ 2 → IsSMulRegular A x)

/- Exercise 111.28.5 (3): a regular local ring of dimension 1 is a domain. -/
@[stacks 02EJ] #check (IsRegularLocalRing.isDomain_of_dim_one :
    ∀ {A : Type u} [CommRing A] [IsRegularLocalRing A], ringKrullDim A = 1 → IsDomain A)
