/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Uses the Euclidean volume argument of Yuanhe Zhang, Jason D. Lee and Fanghui Liu,
SLT/CoveringNumber.lean, commit d0f506f0a695018265dccb33bcb05e2f5ca1c876.
-/
module

public import ReasLib.Analysis.InnerProductSpace.Euclidean.Packing

@[expose] public section

/-!
# Packing and internal covers in finite-dimensional real inner-product spaces

A finite-dimensional real inner-product space is transported to Euclidean space
by `(stdOrthonormalBasis ℝ E).repr`; the exponent is exactly `Module.finrank ℝ E`.
Translation treats balls about arbitrary centers. Dimension zero is included by
the Euclidean theorem's separate subsingleton branch.

For **any** subset of a closed ball, the cover constructed here has centers in
that subset. Neither closedness nor finiteness of the subset is assumed. The
cardinal bound is `(1 + 2 * R / ε) ^ finrank ℝ E`, with the original radius and
constant. Strictly separated packing centers yield a net by **closed** balls.

Applications include geometry of numbers, metric entropy, numerical finite nets,
and height counting once a real inner-product-space realization is supplied.
No height pairing, torsion quotient, or group-rank comparison is assumed or
constructed here. We make no assertion for arbitrary norms.
-/

open Set Metric
open scoped NNReal ENNReal

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exact packing bound transported by an orthonormal-coordinate linear isometry.
This theorem also holds when `finrank ℝ E = 0`. -/
theorem finset_card_le_of_isSeparated {t : Finset E} {c : E} {R : ℝ} {ε : ℝ≥0}
    (hR : 0 ≤ R) (hε : 0 < ε) (hsub : (t : Set E) ⊆ closedBall c R)
    (hsep : Metric.IsSeparated (ε : ℝ≥0∞) (t : Set E)) :
    (t.card : ℝ) ≤ (1 + 2 * R / (ε : ℝ)) ^ Module.finrank ℝ E := by
  classical
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (stdOrthonormalBasis ℝ E).repr
  let f : E → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun x => e (x - c)
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (e (x - c)) (e (y - c)) = dist x y
    rw [e.isometry.dist_eq]
    simp [dist_eq_norm]
  have hsub' : (t.image f : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) ⊆
      closedBall 0 R := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_closedBall, dist_zero_right]
    change ‖e (a - c)‖ ≤ R
    rw [e.norm_map]
    simpa only [dist_eq_norm] using mem_closedBall.mp (hsub ha)
  have hsep' : Metric.IsSeparated (ε : ℝ≥0∞)
      (t.image f : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [Metric.isSeparated_iff_pairwise_dist] at hsep ⊢
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [hf.dist_eq]
    exact hsep ha hb (fun h => hxy (congrArg f h))
  have hbound := EuclideanSpace.finset_card_le_of_isSeparated hR hε hsub' hsep'
  simpa [Finset.card_image_of_injective t hf.injective] using hbound

/-- Internal finite cover of an arbitrary subset of a ball, with the exact
volumetric cardinal bound. The centers form a maximum-cardinality separated
subset of the actual set being covered. -/
theorem exists_finset_isCover_card_le {s : Set E} {c : E} {R : ℝ} {ε : ℝ≥0}
    (hR : 0 ≤ R) (hε : 0 < ε) (hs : s ⊆ closedBall c R) :
    ∃ t : Finset E, (t : Set E) ⊆ s ∧
      Metric.IsSeparated (ε : ℝ≥0∞) (t : Set E) ∧ Metric.IsCover ε s (t : Set E) ∧
      (t.card : ℝ) ≤ (1 + 2 * R / (ε : ℝ)) ^ Module.finrank ℝ E := by
  have htb : TotallyBounded s := (isCompact_closedBall c R).totallyBounded.subset hs
  obtain ⟨t, hsub, hsep, hcover, _⟩ :=
    Metric.exists_finset_isSeparated_isCover hε.ne' htb
  exact ⟨t, hsub, hsep, hcover, finset_card_le_of_isSeparated hR hε (hsub.trans hs) hsep⟩

/-- A real-radius interface to the internal cover theorem. Every center lies in
`s`, and every point of `s` is at distance at most `r` from a center. -/
theorem exists_finset_cover_card_le {s : Set E} {c : E} {R r : ℝ}
    (hR : 0 ≤ R) (hr : 0 < r) (hs : s ⊆ closedBall c R) :
    ∃ t : Finset E, (t : Set E) ⊆ s ∧
      (∀ x ∈ s, ∃ y ∈ t, dist x y ≤ r) ∧
      (t.card : ℝ) ≤ (1 + 2 * R / r) ^ Module.finrank ℝ E := by
  obtain ⟨t, hsub, _, hcover, hcard⟩ :=
    exists_finset_isCover_card_le (ε := ⟨r, hr.le⟩) hR (by exact hr) hs
  exact ⟨t, hsub, Metric.isCover_iff_forall_exists_dist.mp hcover, hcard⟩

/-- The canonical **internal** covering number is finite under the ball hypothesis.
This records the non-top hypothesis needed before reading its `toNat` value. -/
theorem coveringNumber_ne_top_of_subset_closedBall {s : Set E} {c : E} {R : ℝ}
    {ε : ℝ≥0} (hε : ε ≠ 0) (hs : s ⊆ closedBall c R) :
    Metric.coveringNumber ε s ≠ ⊤ := by
  have htb : TotallyBounded s := (isCompact_closedBall c R).totallyBounded.subset hs
  exact ne_top_of_le_ne_top (Metric.packingNumber_ne_top_of_totallyBounded hε htb)
    (Metric.coveringNumber_le_packingNumber ε s)

/-- Exact bound for the natural value of Mathlib's internal covering number.
The accompanying non-top result prevents interpreting `toNat ⊤ = 0` as a bound. -/
theorem coveringNumber_toNat_le {s : Set E} {c : E} {R : ℝ} {ε : ℝ≥0}
    (hR : 0 ≤ R) (hε : 0 < ε) (hs : s ⊆ closedBall c R) :
    ((Metric.coveringNumber ε s).toNat : ℝ) ≤
      (1 + 2 * R / (ε : ℝ)) ^ Module.finrank ℝ E := by
  obtain ⟨t, hsub, _, hcover, hcard⟩ := exists_finset_isCover_card_le hR hε hs
  have hle : Metric.coveringNumber ε s ≤ (t.card : ℕ∞) := by
    simpa using hcover.coveringNumber_le_encard hsub
  have hnat : (Metric.coveringNumber ε s).toNat ≤ t.card := by
    have hc := (ENat.coe_toNat_le_self (Metric.coveringNumber ε s)).trans hle
    exact_mod_cast hc
  exact (Nat.cast_le.mpr hnat).trans hcard

/-- Dimension zero needs one center for a nonempty set and zero centers for an
empty set. It remains valid even at covering radius zero. -/
theorem exists_finset_cover_card_le_one_of_finrank_eq_zero (hE : Module.finrank ℝ E = 0)
    (s : Set E) (r : ℝ) (hr : 0 ≤ r) :
    ∃ t : Finset E, (t : Set E) ⊆ s ∧
      (∀ x ∈ s, ∃ y ∈ t, dist x y ≤ r) ∧ t.card ≤ 1 := by
  classical
  haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨∅, by simp, by simp, by simp⟩
  · refine ⟨{a}, by simpa, ?_, by simp⟩
    intro x hx
    refine ⟨a, by simp, ?_⟩
    simpa [Subsingleton.elim x a] using hr

end InnerProductSpace

end
