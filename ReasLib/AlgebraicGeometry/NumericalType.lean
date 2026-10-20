/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Matrix.Basic

@[expose] public section

open scoped BigOperators

/-- A numerical type consists of finite indexed multiplicities, an integral intersection matrix,
positive weights, and nonnegative component genera satisfying the numerical type relations. -/
public structure NumericalType where
  /-- The number of indices. -/
  n : ℕ
  /-- The number of indices is positive. -/
  n_pos : 0 < n
  /-- The multiplicity attached to each index. -/
  multiplicity : Fin n → ℕ
  /-- The integral intersection matrix. -/
  intersection : Matrix (Fin n) (Fin n) ℤ
  /-- The weight attached to each index. -/
  weight : Fin n → ℕ
  /-- The component genus attached to each index. -/
  componentGenus : Fin n → ℕ
  /-- Every multiplicity is positive. -/
  multiplicity_pos : ∀ i, 0 < multiplicity i
  /-- Every weight is positive. -/
  weight_pos : ∀ i, 0 < weight i
  /-- The intersection matrix is symmetric. -/
  symmetric : ∀ i j, intersection i j = intersection j i
  /-- Off-diagonal entries of the intersection matrix are nonnegative. -/
  offDiagonal_nonnegative : ∀ i j, i ≠ j → 0 ≤ intersection i j
  /-- Every nonempty proper set of indices meets its complement through a nonzero intersection. -/
  connected : ∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
    ∃ i ∈ I, ∃ j ∉ I, intersection i j ≠ 0
  /-- The multiplicity vector lies in the kernel of the intersection matrix. -/
  rowSum_eq_zero : ∀ i, ∑ j, intersection i j * (multiplicity j : ℤ) = 0
  /-- The weight at each index divides every entry in the corresponding row. -/
  weight_dvd : ∀ i j, (weight i : ℤ) ∣ intersection i j

namespace NumericalType

/-- Construct a numerical type from its indexed data and defining conditions. -/
public def of (n : ℕ) (n_pos : 0 < n)
    (multiplicity weight componentGenus : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ)
    (multiplicity_pos : ∀ i, 0 < multiplicity i)
    (weight_pos : ∀ i, 0 < weight i)
    (symmetric : ∀ i j, intersection i j = intersection j i)
    (offDiagonal_nonnegative : ∀ i j, i ≠ j → 0 ≤ intersection i j)
    (connected : ∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, intersection i j ≠ 0)
    (rowSum_eq_zero : ∀ i, ∑ j, intersection i j * (multiplicity j : ℤ) = 0)
    (weight_dvd : ∀ i j, (weight i : ℤ) ∣ intersection i j) : NumericalType :=
  { n, n_pos, multiplicity, intersection, weight, componentGenus,
    multiplicity_pos, weight_pos, symmetric, offDiagonal_nonnegative,
    connected, rowSum_eq_zero, weight_dvd }

end NumericalType
