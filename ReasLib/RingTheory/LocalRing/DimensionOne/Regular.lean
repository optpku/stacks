/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

universe u

open IsLocalRing

namespace IsRegularLocalRing

/-- In a regular local ring of Krull dimension one, every nonzero element of the maximal
ideal is a unit times a natural power of any maximal-ideal element outside its square. -/
theorem exists_unit_mul_pow_of_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 1)
    {x : A} (hx_mem : x ∈ maximalIdeal A) (hx : x ∉ maximalIdeal A ^ 2)
    {y : A} (hy_mem : y ∈ maximalIdeal A) (hy : y ≠ 0) :
    ∃ n : ℕ, ∃ u : Aˣ, y = u * x ^ n := sorry

/-- In a regular local ring of Krull dimension one, every maximal-ideal element outside
the square of the maximal ideal is a nonzerodivisor. -/
theorem isSMulRegular_of_not_mem_sq
    {A : Type u} [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 1)
    {x : A} (hx_mem : x ∈ maximalIdeal A) (hx : x ∉ maximalIdeal A ^ 2) :
    IsSMulRegular A x := sorry

/-- A regular local ring of Krull dimension one is a domain. -/
theorem isDomain_of_dim_one
    {A : Type u} [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 1) :
    IsDomain A := sorry

end IsRegularLocalRing
