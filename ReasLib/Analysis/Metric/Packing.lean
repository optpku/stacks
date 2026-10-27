/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Metric interface for the packing argument adapted from
Yuanhe Zhang, Jason D. Lee and Fanghui Liu, SLT/CoveringNumber.lean,
commit d0f506f0a695018265dccb33bcb05e2f5ca1c876 (Apache-2.0).
The canonical predicates and cardinal invariants are owned by Mathlib.
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Finite maximal packings and internal covers

The data in this file are Mathlib's `Metric.IsSeparated`, `Metric.IsCover`, and
`Metric.maximalSeparatedSet`. Separation is strict (`ε < dist x y`); covers use
closed balls (`dist x y ≤ ε`). Radii are nonnegative reals. Cardinal invariants
remain Mathlib's `ℕ∞`; in particular `coveringNumber` is the **internal** covering
number, whereas the source's global `coveringNumber` is an external one.

No finite-dimensional or linear structure is needed. The same interface applies
to metric entropy, finite discretizations of compact spaces, and numerical nets.
-/

open Set
open scoped NNReal ENNReal

namespace Metric

variable {X : Type*}

section PseudoMetricSpace

variable [PseudoMetricSpace X] {s C : Set X} {ε : ℝ≥0}

/-- The strict distance convention for Mathlib separated sets. -/
lemma isSeparated_iff_pairwise_dist :
    IsSeparated (ε : ℝ≥0∞) C ↔ C.Pairwise (fun x y => (ε : ℝ) < dist x y) := by
  simp [IsSeparated, edist_dist]

/-- Closed-ball nets written with ordinary distance. Centers need not lie in the
covered set; that condition is supplied separately for internal covers. -/
lemma isCover_iff_forall_exists_dist :
    IsCover ε s C ↔ ∀ x ∈ s, ∃ y ∈ C, dist x y ≤ (ε : ℝ) := by
  rw [isCover_iff_subset_iUnion_closedBall]
  simp [Set.subset_def]

end PseudoMetricSpace

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] {s : Set X} {ε : ℝ≥0}

/-- Total boundedness bounds the cardinalities of all strictly separated subsets.
The half-radius cover is used only to establish finiteness, not for the final
covering radius or the finite-dimensional constant. -/
lemma packingNumber_ne_top_of_totallyBounded (hε : ε ≠ 0) (hs : TotallyBounded s) :
    packingNumber ε s ≠ ⊤ := by
  obtain ⟨C, _, hC, hcover⟩ :=
    exists_finite_isCover_of_totallyBounded (ε := ε / 2) (by positivity) hs
  have hbound : packingNumber ε s ≤ C.encard := by
    calc
      packingNumber ε s = packingNumber (2 * (ε / 2)) s := by congr 1; ring
      _ ≤ externalCoveringNumber (ε / 2) s :=
        packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ C.encard := hcover.externalCoveringNumber_le_encard
  exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hC) hbound

/-- A totally bounded set has a finite maximum-cardinality separated subset which
is a closed-ball net, with centers in the original set. This is a finite view of
Mathlib's `maximalSeparatedSet`, not a second owner of maximal-packing data. -/
theorem exists_finset_isSeparated_isCover (hε : ε ≠ 0) (hs : TotallyBounded s) :
    ∃ t : Finset X, (t : Set X) ⊆ s ∧ IsSeparated (ε : ℝ≥0∞) (t : Set X) ∧
      IsCover ε s (t : Set X) ∧ (t.card : ℕ∞) = packingNumber ε s := by
  classical
  have htop := packingNumber_ne_top_of_totallyBounded hε hs
  have hfin : (maximalSeparatedSet ε s).Finite := by
    apply Set.encard_ne_top_iff.mp
    rw [encard_maximalSeparatedSet htop]
    exact htop
  refine ⟨hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · simpa using (maximalSeparatedSet_subset (ε := ε) (A := s))
  · simpa using (isSeparated_maximalSeparatedSet (ε := ε) (A := s))
  · simpa using (isCover_maximalSeparatedSet htop)
  · rw [← hfin.encard_eq_coe_toFinset_card]
    exact encard_maximalSeparatedSet htop

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace X] {s C : Set X} {ε : ℝ≥0}

/-- Ordinary-distance form of the finite internal maximal-packing cover. -/
theorem exists_finset_pairwise_dist_cover (hε : ε ≠ 0) (hs : TotallyBounded s) :
    ∃ t : Finset X, (t : Set X) ⊆ s ∧
      (t : Set X).Pairwise (fun x y => (ε : ℝ) < dist x y) ∧
      (∀ x ∈ s, ∃ y ∈ t, dist x y ≤ (ε : ℝ)) := by
  obtain ⟨t, hsub, hsep, hcover, _⟩ := exists_finset_isSeparated_isCover hε hs
  exact ⟨t, hsub, isSeparated_iff_pairwise_dist.mp hsep,
    isCover_iff_forall_exists_dist.mp hcover⟩

/-- Strict separation gives disjoint closed half-radius balls, without changing
strict separation into a non-strict inequality. -/
lemma IsSeparated.pairwiseDisjoint_closedBall_half (hsep : IsSeparated (ε : ℝ≥0∞) C) :
    C.PairwiseDisjoint (fun x => closedBall x ((ε : ℝ) / 2)) := by
  intro x hx y hy hxy
  apply closedBall_disjoint_closedBall
  have hdist := isSeparated_iff_pairwise_dist.mp hsep hx hy hxy
  linarith

end PseudoMetricSpace

end Metric
