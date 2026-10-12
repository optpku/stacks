/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Lattice
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
      w (Fin.last n) = 1 ∧ tailDominates spread w := sorry

/-- The defining nonempty-set expression for `coordinateSpread`. -/
theorem coordinateSpread_eq (N : Finset (σ →₀ ℕ)) (hN : N.Nonempty) (i : σ) :
    coordinateSpread N i = N.sup (fun ν ↦ ν i) - N.inf' hN (fun ν ↦ ν i) := sorry

/-- The coordinate spread is bounded by the corresponding pairwise spread. -/
theorem coordinateSpread_le_pairSpread
    (N : Finset (σ →₀ ℕ)) (i : σ) :
    coordinateSpread N i ≤ pairSpread N i := sorry

/-- Over a finite index type, `Finsupp.weight` is the full coordinate sum. -/
theorem weight_eq_sum_univ [Fintype σ] (ν : σ →₀ ℕ) (e : σ → ℕ) :
    ν.weight e = ∑ j : σ, ν j * e j := sorry

/-- A coordinate of one multi-index is bounded by the corresponding coordinate of another one
plus the coordinate spread of a common finite set. -/
theorem coordinate_le_add_coordinateSpread
    (N : Finset (σ →₀ ℕ)) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N) (i : σ) :
    ν i ≤ ν' i + coordinateSpread N i := sorry

/-- The weighted contribution after `i` is bounded by the corresponding contribution of another
multi-index plus the tail coordinate-spread bound. -/
theorem tail_weight_le_add_spread
    [Fintype σ] [LT σ] [DecidableRel (fun i j : σ ↦ i < j)]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    (i : σ) :
    Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) ≤
      Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν' j * e j) +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ coordinateSpread N j * e j) := sorry

/-- Split a finite-support weight into the coordinates below a pivot, the pivot coordinate, and
the coordinates above the pivot. -/
theorem weight_split [Fintype σ] [LinearOrder σ] (ν : σ →₀ ℕ) (e : σ → ℕ) (i : σ) :
    ν.weight e =
      Finset.sum (univ.filter (fun j : σ ↦ j < i)) (fun j ↦ ν j * e j) +
        ν i * e i +
        Finset.sum (univ.filter (fun j : σ ↦ i < j)) (fun j ↦ ν j * e j) := sorry

/-- If the first differing coordinate of two multi-indices increases, a dominating weight system
strictly increases their weighted sums. -/
theorem weight_lt_of_first_difference
    [Fintype σ] [LinearOrder σ]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    {i : σ} (hearlier : ∀ j : σ, j < i → ν j = ν' j) (hi : ν i < ν' i)
    (hi_dom :
      e i > Finset.sum (univ.filter fun j : σ ↦ i < j) (fun j ↦ coordinateSpread N j * e j)) :
    ν.weight e < ν'.weight e := sorry

/-- A nonzero natural multi-index has positive weight for a positive weight system. -/
theorem weight_pos_of_ne_zero
    (e : σ → ℕ) (he_pos : ∀ i : σ, 0 < e i) {m : σ →₀ ℕ} (hm : m ≠ 0) :
    0 < m.weight e := sorry

/-- Lemma 10.115.1, tag 051M: tail-dominating weights distinguish the multi-indices in a finite
set by their weighted sums. -/
@[stacks 051M]
theorem weight_eq_iff_eq_of_tailDominates
    [Fintype σ] [LinearOrder σ]
    (N : Finset (σ →₀ ℕ)) (e : σ → ℕ) {ν ν' : σ →₀ ℕ} (hν : ν ∈ N) (hν' : ν' ∈ N)
    (hdom : tailDominates (coordinateSpread N) e) :
    ν.weight e = ν'.weight e ↔ ν = ν' := sorry

end Finsupp
