/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ordered weights on finite sets of multi-indices

This leaf records the finite-coordinate estimates used to turn a lexicographic
comparison of multi-indices into a comparison of weighted sums.
-/

open scoped BigOperators
open Finset

namespace Finsupp

universe u

variable {σ : Type u}

/-- The spread of coordinate `i` among a finite set of natural multi-indices. It is zero when
the set is empty. -/
def coordinateSpread (N : Finset (σ →₀ ℕ)) (i : σ) : ℕ :=
  if hN : N.Nonempty then N.sup (fun ν ↦ ν i) - N.inf' hN (fun ν ↦ ν i) else 0

/-- The pairwise coordinate spread of a finite multi-index set. -/
def pairSpread (N : Finset (σ →₀ ℕ)) (i : σ) : ℕ :=
  (N.product N).sup (fun m ↦ m.1 i - m.2 i)

/-- The weights dominate a prescribed coordinate spread along every strict tail of a relation. -/
def tailDominates [Fintype σ] [LT σ]
    [DecidableRel (fun i j : σ ↦ i < j)] (spread e : σ → ℕ) : Prop :=
  ∀ i : σ,
    e i >
      Finset.sum (univ.filter fun j : σ ↦ i < j)
        (fun j ↦ spread j * e j)

/-- There are weights on `Fin (n + 1)`, normalized to one at the last index, that dominate any
prescribed tail spread. -/
@[stacks 051N "normalized tail-dominating weights"]
theorem exists_tail_dominating_weights {n : ℕ} (spread : Fin (n + 1) → ℕ) :
    ∃ w : Fin (n + 1) → ℕ,
      w (Fin.last n) = 1 ∧ tailDominates spread w := by
  induction n with
  | zero =>
    refine ⟨fun _ ↦ 1, rfl, ?_⟩
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [Finset.sum_filter]
  | succ n ih =>
    obtain ⟨w, hlast, hdom⟩ := ih (fun j ↦ spread j.succ)
    refine ⟨Fin.cons ((∑ j, spread j.succ * w j) + 1) w, ?_, ?_⟩
    · simpa using hlast
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [Finset.sum_filter, Fin.sum_univ_succ]
      · simpa [Finset.sum_filter, Fin.sum_univ_succ] using hdom j

/-- The defining nonempty-set expression for `coordinateSpread`. -/
theorem coordinateSpread_eq (N : Finset (σ →₀ ℕ)) (hN : N.Nonempty) (i : σ) :
    coordinateSpread N i = N.sup (fun ν ↦ ν i) - N.inf' hN (fun ν ↦ ν i) := by
  simp [coordinateSpread, hN]

/-- The coordinate spread is bounded by the corresponding pairwise spread. -/
theorem coordinateSpread_le_pairSpread
    (N : Finset (σ →₀ ℕ)) (i : σ) :
    coordinateSpread N i ≤ pairSpread N i := by
  classical
  by_cases hN : N.Nonempty
  · obtain ⟨ν, hν, hmax⟩ := Finset.exists_mem_eq_sup N hN (fun ν ↦ ν i)
    obtain ⟨ν', hν', hmin⟩ := Finset.exists_mem_eq_inf' hN (fun ν ↦ ν i)
    rw [coordinateSpread_eq N hN i, hmax, hmin]
    exact Finset.le_sup (s := N.product N) (b := (ν, ν'))
      (f := fun m : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ m.1 i - m.2 i)
      (Finset.mem_product.mpr ⟨hν, hν'⟩)
  · simp [coordinateSpread, hN]

/-- Over a finite index type, `Finsupp.weight` is the full coordinate sum. -/
theorem weight_eq_sum_univ [Fintype σ] (ν : σ →₀ ℕ) (e : σ → ℕ) :
    ν.weight e = ∑ j : σ, ν j * e j := by
  rw [weight_apply, Finsupp.sum_fintype ν (fun i c ↦ c • e i) (fun _ ↦ zero_smul _ _)]
  simp [smul_eq_mul]

/-- A coordinate of one multi-index is bounded by the corresponding coordinate of another one
plus the coordinate spread of a common finite set. -/
theorem coordinate_le_add_coordinateSpread
    (N : Finset (σ →₀ ℕ)) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N) (i : σ) :
    ν i ≤ ν' i + coordinateSpread N i := by
  rw [coordinateSpread_eq N ⟨ν, hν⟩ i]
  have hmax := Finset.le_sup (f := fun ν : σ →₀ ℕ ↦ ν i) hν
  have hmin := Finset.inf'_le (fun ν : σ →₀ ℕ ↦ ν i) hν'
  omega

/-- The weighted contribution after `i` is bounded by the corresponding contribution of another
multi-index plus the tail coordinate-spread bound. -/
theorem tail_weight_le_add_spread
    [Fintype σ] [LT σ] [DecidableRel (fun i j : σ ↦ i < j)]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    (i : σ) :
    Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) ≤
      Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν' j * e j) +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ coordinateSpread N j * e j) := by
  calc
    _ ≤ Finset.sum (univ.filter (fun j : σ ↦ i < j))
        (fun j ↦ (ν' j + coordinateSpread N j) * e j) := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_right (e j) (coordinate_le_add_coordinateSpread N hν hν' j)
    _ = _ := by simp [add_mul, Finset.sum_add_distrib]

/-- Split a finite-support weight into the coordinates below a pivot, the pivot coordinate, and
the coordinates above the pivot. -/
theorem weight_split [Fintype σ] [LinearOrder σ] (ν : σ →₀ ℕ) (e : σ → ℕ) (i : σ) :
    ν.weight e =
      Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν j * e j) +
        ν i * e i +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) := by
  have htail : univ.filter (fun j : σ ↦ ¬j < i) =
      insert i (univ.filter (fun j : σ ↦ i < j)) := by
    ext j
    simp [le_iff_eq_or_lt, eq_comm]
  rw [weight_eq_sum_univ,
    ← Finset.sum_filter_add_sum_filter_not univ (fun j : σ ↦ j < i), htail,
    Finset.sum_insert (by simp)]
  exact (add_assoc _ _ _).symm

/-- If the first differing coordinate of two multi-indices increases, a dominating weight system
strictly increases their weighted sums. -/
theorem weight_lt_of_first_difference
    [Fintype σ] [LinearOrder σ]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    {i : σ} (hearlier : ∀ j : σ, j < i → ν j = ν' j) (hi : ν i < ν' i)
    (hi_dom :
      e i > Finset.sum (univ.filter fun j : σ ↦ i < j) (fun j ↦ coordinateSpread N j * e j)) :
    ν.weight e < ν'.weight e := by
  have hbefore :
      Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν j * e j) =
        Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν' j * e j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hearlier j (Finset.mem_filter.mp hj).2]
  have hpivot : ν i * e i + e i ≤ ν' i * e i := by
    simpa [add_mul] using Nat.mul_le_mul_right (e i) (Nat.succ_le_of_lt hi)
  have htail := tail_weight_le_add_spread N e hν hν' i
  rw [weight_split ν e i, weight_split ν' e i, hbefore]
  omega

/-- A nonzero natural multi-index has positive weight for a positive weight system. -/
theorem weight_pos_of_ne_zero
    (e : σ → ℕ) (he_pos : ∀ i : σ, 0 < e i) {m : σ →₀ ℕ} (hm : m ≠ 0) :
    0 < m.weight e := by
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm
  exact (he_pos i).trans_le (le_weight_of_ne_zero' e (by simpa using hi))

/-- Lemma 10.115.1, tag 051M: tail-dominating weights distinguish the multi-indices in a finite
set by their weighted sums. -/
@[stacks 051M]
theorem weight_eq_iff_eq_of_tailDominates
    [Fintype σ] [LinearOrder σ]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    (hdom : tailDominates (coordinateSpread N) e) :
    ν.weight e = ν'.weight e ↔ ν = ν' := by
  classical
  constructor
  · intro hweight
    by_contra hne
    have hs : (univ.filter (fun j : σ ↦ ν j ≠ ν' j)).Nonempty := by
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
      exact ⟨i, Finset.mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ id hs
    have hearlier : ∀ j : σ, j < i → ν j = ν' j := by
      intro j hj
      by_contra hdiff
      exact (not_le_of_gt hj) (hmin j (Finset.mem_filter.mpr ⟨mem_univ _, hdiff⟩))
    rcases lt_or_gt_of_ne (Finset.mem_filter.mp hi).2 with hlt | hgt
    · exact (ne_of_lt (weight_lt_of_first_difference N e hν hν' hearlier hlt (hdom i)))
        hweight
    · exact (ne_of_gt (weight_lt_of_first_difference N e hν' hν
        (fun j hj ↦ (hearlier j hj).symm) hgt (hdom i))) hweight
  · rintro rfl
    rfl

end Finsupp
