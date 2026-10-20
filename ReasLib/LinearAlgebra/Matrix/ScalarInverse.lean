/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

universe u

namespace Matrix

/-- If the product of two square matrices is a power of a natural-number scalar times
the identity, their determinant product is that scalar raised to the rank times the exponent. -/
theorem detProduct_eq_pow
    {R : Type u} [CommRing R] (p r i : ℕ)
    (K L : Matrix (Fin r) (Fin r) R)
    (hKL : K * L = ((p : R) ^ i) • (1 : Matrix (Fin r) (Fin r) R)) :
    K.det * L.det = (p : R) ^ (r * i) := sorry

/-- A one-sided scalar inverse of a square matrix becomes two-sided after multiplying
the reverse matrix by the scalar raised to the rank times the original exponent. -/
theorem powerTwoSided_of_mul_eq
    {R : Type u} [CommRing R] (p r i : ℕ)
    (K L : Matrix (Fin r) (Fin r) R)
    (hKL : K * L = ((p : R) ^ i) • (1 : Matrix (Fin r) (Fin r) R)) :
    let K' : Matrix (Fin r) (Fin r) R := ((p : R) ^ (r * i)) • K
    let j : ℕ := r * i + i
    K' * L = ((p : R) ^ j) • (1 : Matrix (Fin r) (Fin r) R) ∧
      L * K' = ((p : R) ^ j) • (1 : Matrix (Fin r) (Fin r) R) := sorry

/-- For square matrices over a commutative ring, a regular scalar right inverse
is also a left inverse. -/
theorem mul_eq_smul_one_comm {R : Type u} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) :
    B * A = f • 1 := sorry

end Matrix
