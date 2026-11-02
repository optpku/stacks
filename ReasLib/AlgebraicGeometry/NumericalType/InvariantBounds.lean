/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Set.Card
public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality
import all ReasLib.AlgebraicGeometry.NumericalType.Minimality
public import ReasLib.AlgebraicGeometry.NumericalType.TopologicalGenus
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex
public import ReasLib.AlgebraicGeometry.NumericalType.Diagonal
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionBounds
public import ReasLib.AlgebraicGeometry.NumericalType.ProperSubgraphClassification
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace NumericalType

open scoped BigOperators

private theorem offDiagonalSum_eq (T : NumericalType) (j : Fin T.n) :
    (∑ i ∈ Finset.univ.erase j, T.intersection j i * (T.multiplicity i : ℤ)) =
      -T.intersection j j * (T.multiplicity j : ℤ) := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin T.n))
    (fun i ↦ T.intersection j i * (T.multiplicity i : ℤ)) (Finset.mem_univ j)
  have hrow := T.rowSum_eq_zero j
  linarith

private theorem diagonal_neg_for_bounds (T : NumericalType) (hn : 1 < T.n)
    (j : Fin T.n) : T.intersection j j < 0 := by
  have hproper : ({j} : Set (Fin T.n)) ≠ Set.univ := by
    intro h
    have hc := congrArg Set.ncard h
    simp at hc
    omega
  obtain ⟨i, hi, k, hk, hik⟩ := T.connected {j} (by simp) hproper
  have hij : i = j := by simpa using hi
  subst i
  have hkj : k ≠ j := by simpa using hk
  have hpositive : 0 < T.intersection j k :=
    lt_of_le_of_ne (T.offDiagonal_nonnegative j k hkj.symm) (Ne.symm hik)
  have hnonneg : ∀ i ∈ Finset.univ.erase j,
      0 ≤ T.intersection j i * (T.multiplicity i : ℤ) := by
    intro i hi
    exact mul_nonneg
      (T.offDiagonal_nonnegative j i (Finset.ne_of_mem_erase hi).symm)
      (Int.natCast_nonneg _)
  have hsingle := Finset.single_le_sum hnonneg (by simp [hkj] : k ∈ Finset.univ.erase j)
  have hmk : (0 : ℤ) < T.multiplicity k := by exact_mod_cast T.multiplicity_pos k
  have hmj : (0 : ℤ) < T.multiplicity j := by exact_mod_cast T.multiplicity_pos j
  have hterm := mul_pos hpositive hmk
  rw [offDiagonalSum_eq] at hsingle
  nlinarith

/-- Work with twice each genus contribution, so every summand is integral. -/
private theorem twiceContribution_bounds (T : NumericalType) (hminimal : T.IsMinimal)
    (hn : 1 < T.n) (j : Fin T.n) :
    let C := (T.multiplicity j : ℤ) *
      (2 * (T.weight j : ℤ) * ((T.componentGenus j : ℤ) - 1) - T.intersection j j)
    0 ≤ C ∧ 2 * ((T.componentGenus j : ℤ) - 1) < C ∧
      (¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j →
        1 ≤ C ∧ (T.multiplicity j : ℤ) * |T.intersection j j| ≤ 3 * C) := by
  dsimp only
  have hm : (1 : ℤ) ≤ T.multiplicity j := by
    have h := T.multiplicity_pos j
    omega
  have hw : (1 : ℤ) ≤ T.weight j := by
    have h := T.weight_pos j
    omega
  have hd := diagonal_neg_for_bounds T hn j
  rw [abs_of_neg hd]
  by_cases hc : T.componentGenus j = 0
  · obtain ⟨k, hk⟩ := T.weight_dvd j j
    have hkneg : k ≤ -1 := by nlinarith
    have hnotone : k ≠ -1 := by
      intro hkone
      apply hminimal
      refine ⟨j, hc, ?_⟩
      rw [hk, hkone]
      ring
    have hk_le : k ≤ -2 := by omega
    simp only [hc, Nat.cast_zero, zero_sub, mul_neg, mul_one]
    have hbracket : 0 ≤ -(2 * (T.weight j : ℤ)) - T.intersection j j := by
      nlinarith
    have hC := mul_nonneg (by omega : (0 : ℤ) ≤ T.multiplicity j) hbracket
    refine ⟨hC, by omega, ?_⟩
    intro hj
    have hnottwo : k ≠ -2 := by
      intro hktwo
      apply hj
      refine ⟨hc, ?_⟩
      rw [hk, hktwo]
      ring
    have hk_le_three : k ≤ -3 := by omega
    have hbracket_one : 1 ≤ -(2 * (T.weight j : ℤ)) - T.intersection j j := by
      nlinarith
    have hbracket_three :
        -T.intersection j j ≤ 3 * (-(2 * (T.weight j : ℤ)) - T.intersection j j) := by
      nlinarith
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hbracket_one)]
    · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ T.multiplicity j)
        (sub_nonneg.mpr hbracket_three)]
  · have hcpos : (1 : ℤ) ≤ T.componentGenus j := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
    have hbracket : 2 * ((T.componentGenus j : ℤ) - 1) + 1 ≤
        2 * (T.weight j : ℤ) * ((T.componentGenus j : ℤ) - 1) - T.intersection j j := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hcpos)]
    have hC : 2 * (T.weight j : ℤ) * ((T.componentGenus j : ℤ) - 1) -
        T.intersection j j ≤ (T.multiplicity j : ℤ) *
          (2 * (T.weight j : ℤ) * ((T.componentGenus j : ℤ) - 1) -
            T.intersection j j) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm)
        (by linarith : 0 ≤ 2 * (T.weight j : ℤ) *
          ((T.componentGenus j : ℤ) - 1) - T.intersection j j)]
    refine ⟨by omega, by omega, fun _ ↦ ⟨by omega, ?_⟩⟩
    have hproduct := mul_nonneg (by omega : (0 : ℤ) ≤ T.multiplicity j)
      (mul_nonneg (by omega : (0 : ℤ) ≤ T.weight j) (sub_nonneg.mpr hcpos))
    nlinarith

private theorem sum_twiceContribution_le (T : NumericalType) :
    (∑ i, (T.multiplicity i : ℤ) *
      (2 * (T.weight i : ℤ) * ((T.componentGenus i : ℤ) - 1) - T.intersection i i)) ≤
      2 * T.genus - 2 := by
  have heq : (∑ i, (T.multiplicity i : ℤ) *
      (2 * (T.weight i : ℤ) * ((T.componentGenus i : ℤ) - 1) - T.intersection i i)) =
      2 * (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.componentGenus i : ℤ) - 1)) -
      ∑ i, (T.multiplicity i : ℤ) * T.intersection i i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdiv := Int.ediv_mul_le
    (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) (by decide : (2 : ℤ) ≠ 0)
  rw [heq, genus]
  omega

private theorem twiceContribution_le (T : NumericalType) (hminimal : T.IsMinimal)
    (hn : 1 < T.n) (j : Fin T.n) :
    (T.multiplicity j : ℤ) *
      (2 * (T.weight j : ℤ) * ((T.componentGenus j : ℤ) - 1) - T.intersection j j) ≤
      2 * T.genus - 2 := by
  exact (Finset.single_le_sum
    (fun i _ ↦ (twiceContribution_bounds T hminimal hn i).1)
    (Finset.mem_univ j)).trans (sum_twiceContribution_le T)

/-- The non-`(-2)` indices of a minimal numerical type of genus `g ≥ 2` have
cardinality at most `2 * g - 2` when the type has more than one index. -/
public theorem nonMinusTwoIndexCardBound (g : ℤ) (hg : 2 ≤ g) (T : NumericalType)
    (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n) :
    (Set.ncard {j : Fin T.n |
      ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j} : ℤ) ≤ 2 * g - 2 := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  calc
    _ = ∑ _ ∈ {j : Fin T.n |
        ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j}.toFinset, (1 : ℤ) := by
      simp
    _ ≤ ∑ j ∈ {j : Fin T.n |
        ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j}.toFinset,
        (T.multiplicity j : ℤ) *
          (2 * (T.weight j : ℤ) * ((T.componentGenus j : ℤ) - 1) -
            T.intersection j j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ((twiceContribution_bounds T hminimal hn j).2.2 (by simpa using hj)).1
    _ ≤ ∑ j, (T.multiplicity j : ℤ) *
        (2 * (T.weight j : ℤ) * ((T.componentGenus j : ℤ) - 1) - T.intersection j j) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ ↦ (twiceContribution_bounds T hminimal hn j).1)
    _ ≤ 2 * T.genus - 2 := sum_twiceContribution_le T
    _ = 2 * g - 2 := by rw [hgenus]

/-- Every non-`(-2)` index of a minimal numerical type of genus `g ≥ 2` has
component genus strictly less than `g` when the type has more than one index. -/
public theorem componentGenusBoundOfNotMinusTwo (g : ℤ) (hg : 2 ≤ g)
    (T : NumericalType) (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n)
    (j : Fin T.n)
    (hj : ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j) :
    (T.componentGenus j : ℤ) < g := by
  have hlocal := (twiceContribution_bounds T hminimal hn j).2.1
  have htotal := twiceContribution_le T hminimal hn j
  rw [hgenus] at htotal
  omega

/-- The multiplicity-weighted absolute diagonal intersection at a non-`(-2)` index
of a minimal numerical type of genus `g ≥ 2` is at most `6 * g - 6`. -/
public theorem diagonalBoundOfNotMinusTwo (g : ℤ) (hg : 2 ≤ g) (T : NumericalType)
    (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n) (j : Fin T.n)
    (hj : ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j) :
    (T.multiplicity j : ℤ) * |T.intersection j j| ≤ 6 * g - 6 := by
  have hlocal := ((twiceContribution_bounds T hminimal hn j).2.2 hj).2
  have htotal := twiceContribution_le T hminimal hn j
  rw [hgenus] at htotal
  linarith

/-- For a non-`(-2)` target index `j` of a minimal numerical type of genus `g ≥ 2`,
every multiplicity-weighted intersection with `j` is at most `6 * g - 6`. -/
public theorem intersectionBoundOfNotMinusTwo (g : ℤ) (hg : 2 ≤ g)
    (T : NumericalType) (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n)
    (j : Fin T.n) (hj : ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j)
    (i : Fin T.n) :
    (T.multiplicity i : ℤ) * T.intersection i j ≤ 6 * g - 6 := by
  have hdiag := diagonalBoundOfNotMinusTwo g hg T hgenus hminimal hn j hj
  by_cases hij : i = j
  · subst i
    exact (mul_le_mul_of_nonneg_left (le_abs_self _)
      (Int.natCast_nonneg _)).trans hdiag
  · have hsingle : T.intersection j i * (T.multiplicity i : ℤ) ≤
        ∑ k ∈ Finset.univ.erase j, T.intersection j k * (T.multiplicity k : ℤ) := by
      apply Finset.single_le_sum (s := Finset.univ.erase j)
        (f := fun k ↦ T.intersection j k * (T.multiplicity k : ℤ))
      · intro k hk
        exact mul_nonneg
          (T.offDiagonal_nonnegative j k (Finset.ne_of_mem_erase hk).symm)
          (Int.natCast_nonneg _)
      · simp [hij]
    rw [offDiagonalSum_eq, T.symmetric j i] at hsingle
    have hneg := mul_le_mul_of_nonneg_left (neg_le_abs (T.intersection j j))
      (Int.natCast_nonneg (T.multiplicity j))
    nlinarith

/-- The genus of a minimal numerical type with more than one index is at least
its topological genus. -/
public theorem topologicalGenus_le_genus (T : NumericalType) (hminimal : T.IsMinimal)
    (hn : 1 < T.n) : (T.topologicalGenus : ℤ) ≤ T.genus := sorry

/-- For a minimal numerical type of genus `g ≥ 2`, every multiplicity-weighted
absolute intersection is at most `768 * g`. -/
public theorem absoluteIntersectionBound (g : ℤ) (hg : 2 ≤ g) (T : NumericalType)
    (hgenus : T.genus = g) (hminimal : T.IsMinimal) (i j : Fin T.n) :
    (T.multiplicity i : ℤ) * |T.intersection i j| ≤ 768 * g := sorry

end NumericalType
