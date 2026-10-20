/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Subsequence Extraction for Sequential Diagrams

Given a strictly increasing function `s : ℕ → ℕ` (representing a subsequence extraction),
this module provides the combinatorial backbone for relating a sequential diagram to its
extracted subsequence. The key definition is `nextSelectedIndex s n`, the least index `i`
such that `s i ≥ n`, which governs how to "round up" an arbitrary stage to the nearest
selected stage.

These results are used in the telescope comparison machinery (homotopy colimits of
subsequences are homotopy colimits of the original sequence).

## Main definitions

* `Subsequence.nextSelectedIndex` — the least `i` with `n ≤ s i`.

## Main results

* `Subsequence.le_strictMono_self` — a strictly increasing function dominates the identity.
* `Subsequence.le_nextSelectedStage` — the selected stage lies above the input.
* `Subsequence.nextSelectedIndex_minimal` — minimality of `nextSelectedIndex`.
* `Subsequence.nextSelectedIndex_of_stage` — at stage `s i`, the next selected index is `i`.
* `Subsequence.nextSelectedIndex_succ_of_not_selected` — stepping past non-selected stages.
* `Subsequence.nextSelectedIndex_of_stage_succ` — stepping past a selected stage.
-/

namespace Subsequence

/-- A strictly increasing sequence on `ℕ` dominates the identity: `n ≤ s n` for all `n`. -/
theorem le_strictMono_self {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    n ≤ s n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    exact le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt (hs (Nat.lt_succ_self n)))

/-- Every natural number lies below some selected subsequence stage. -/
theorem exists_selected_ge {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    ∃ i, n ≤ s i :=
  ⟨n, le_strictMono_self hs n⟩

/-- The least subsequence index whose stage is at least `n`. -/
def nextSelectedIndex (s : ℕ → ℕ) (hs : StrictMono s) (n : ℕ) : ℕ :=
  Nat.find (exists_selected_ge hs n)

/-- The chosen selected stage lies above the original stage. -/
theorem le_nextSelectedStage {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    n ≤ s (nextSelectedIndex s hs n) :=
  Nat.find_spec (exists_selected_ge hs n)

/-- The chosen selected index is minimal among indices whose stage lies above `n`. -/
theorem nextSelectedIndex_minimal {s : ℕ → ℕ} (hs : StrictMono s) (n i : ℕ)
    (hi : n ≤ s i) :
    nextSelectedIndex s hs n ≤ i :=
  Nat.find_min' (exists_selected_ge hs n) hi

/-- At a selected stage `s i`, the least selected index above it is exactly `i`. -/
theorem nextSelectedIndex_of_stage {s : ℕ → ℕ} (hs : StrictMono s) (i : ℕ) :
    nextSelectedIndex s hs (s i) = i := by
  apply le_antisymm
  · exact nextSelectedIndex_minimal hs (s i) i le_rfl
  · exact Nat.le_of_not_lt fun hlt ↦
      not_lt_of_ge (le_nextSelectedStage hs (s i)) (hs hlt)

/-- If `s i = n`, then the chosen selected index above `n` is `i`. -/
theorem nextSelectedIndex_eq_of_eq {s : ℕ → ℕ} (hs : StrictMono s) {i n : ℕ}
    (h : s i = n) :
    nextSelectedIndex s hs n = i := by
  simpa [h] using nextSelectedIndex_of_stage hs i

/-- Once a stage is not selected, the next stage has the same chosen selected index. -/
theorem nextSelectedIndex_succ_of_not_selected {s : ℕ → ℕ} (hs : StrictMono s) {n : ℕ}
    (hsel : ¬ ∃ i, s i = n) :
    nextSelectedIndex s hs (n + 1) = nextSelectedIndex s hs n := by
  apply le_antisymm
  · apply nextSelectedIndex_minimal hs (n + 1) (nextSelectedIndex s hs n)
    have hlt : n < s (nextSelectedIndex s hs n) :=
      lt_of_le_of_ne (le_nextSelectedStage hs n) fun hEq ↦
        hsel ⟨nextSelectedIndex s hs n, hEq.symm⟩
    exact Nat.succ_le_of_lt hlt
  · apply nextSelectedIndex_minimal hs n (nextSelectedIndex s hs (n + 1))
    exact le_trans (Nat.le_succ n) (le_nextSelectedStage hs (n + 1))

/-- The stage immediately after `s i` is controlled by the next selected index `i + 1`. -/
theorem nextSelectedIndex_of_stage_succ {s : ℕ → ℕ} (hs : StrictMono s) (i : ℕ) :
    nextSelectedIndex s hs (s i + 1) = i + 1 := by
  apply le_antisymm
  · apply nextSelectedIndex_minimal hs (s i + 1) (i + 1)
    exact Nat.succ_le_of_lt (hs (Nat.lt_succ_self i))
  · exact Nat.le_of_not_lt fun hlt ↦
      let hle : nextSelectedIndex s hs (s i + 1) ≤ i := Nat.lt_succ_iff.mp hlt
      have hstage := le_nextSelectedStage hs (s i + 1)
      have hsle : s (nextSelectedIndex s hs (s i + 1)) ≤ s i := hs.monotone hle
      Nat.not_succ_le_self (s i) (le_trans hstage hsle)

/-- The selected index is monotone: if `m ≤ n`, then `nextSelectedIndex s hs m ≤ nextSelectedIndex s hs n`. -/
theorem nextSelectedIndex_mono {s : ℕ → ℕ} (hs : StrictMono s) :
    Monotone (nextSelectedIndex s hs) := by
  intro m n hmn
  apply nextSelectedIndex_minimal hs m
  exact le_trans hmn (le_nextSelectedStage hs n)

end Subsequence
