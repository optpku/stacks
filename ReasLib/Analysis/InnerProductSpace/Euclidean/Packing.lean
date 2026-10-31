/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Adapted from SLT/CoveringNumber.lean at
 d0f506f0a695018265dccb33bcb05e2f5ca1c876 (Apache-2.0).
Changes: Mathlib metric predicates, restricted imports, arbitrary-subset packing
interface, and a separate dimension-zero branch.
-/
module

public import ReasLib.Analysis.Metric.Packing
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# Euclidean volume counting for strictly separated finite sets

This module contains the Euclidean volume argument only. The finite-dimensional
inner-product-space transport and the internal-cover application are in
`ReasLib.Analysis.InnerProductSpace.Packing`.

The proof uses disjoint **closed** balls of radius `ε / 2`. Their disjointness
uses **strict** separation. The exact cardinal bound is `(1 + 2 * R / ε)^d`.
The empty coordinate type is handled using subsingleton cardinality, without
using a positive-dimensional volume formula at dimension zero.

The argument is the standard volumetric packing proof; see Vershynin,
*High-Dimensional Probability*, Section 4.2, and the source above.
-/

noncomputable section

open Set Metric MeasureTheory Finset
open scoped NNReal ENNReal

namespace EuclideanSpace

section PositiveDimension

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The constant factor in the volume of a unit ball. -/
private noncomputable def ballVolumeFactor (d : ℕ) : ℝ :=
  Real.pi.sqrt ^ d / Real.Gamma (d / 2 + 1)

private lemma ballVolumeFactor_pos (d : ℕ) : 0 < ballVolumeFactor d := by
  unfold ballVolumeFactor
  apply div_pos
  · exact pow_pos (Real.sqrt_pos.mpr Real.pi_pos) d
  · have h : (0 : ℝ) < (d : ℝ) / 2 + 1 := by positivity
    exact Real.Gamma_pos_of_pos h

/-- The volume of a closed ball with radius r equals r^d times the unit ball volume. -/
private lemma volume_closedBall_eq_pow_mul_factor (x : EuclideanSpace ℝ ι) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume (Metric.closedBall x r) =
    ENNReal.ofReal (r ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) := by
  rw [EuclideanSpace.volume_closedBall]
  have hr_pow : ENNReal.ofReal r ^ Fintype.card ι = ENNReal.ofReal (r ^ Fintype.card ι) := by
    induction Fintype.card ι with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      rw [mul_comm (ENNReal.ofReal _) (ENNReal.ofReal r)]
      rw [← ENNReal.ofReal_mul hr]
      rw [mul_comm r (r ^ n)]
  rw [hr_pow]
  unfold ballVolumeFactor
  rw [← ENNReal.ofReal_mul (pow_nonneg hr _)]

/-- Key cardinality bound: For a packing in B(0, R), we have
    |t| ≤ ((R + ε/2) / (ε/2))^d = (1 + 2R/ε)^d -/
private lemma finset_card_le_radius_ratio
    {t : Finset (EuclideanSpace ℝ ι)} {R : ℝ} {eps : ℝ≥0}
    (hR : 0 ≤ R) (heps : 0 < eps)
    (hsub : (t : Set (EuclideanSpace ℝ ι)) ⊆ Metric.closedBall 0 R)
    (hpacking : Metric.IsSeparated (eps : ℝ≥0∞) (t : Set (EuclideanSpace ℝ ι))) :
    (t.card : ℝ) ≤ ((R + (eps : ℝ) / 2) / ((eps : ℝ) / 2)) ^ Fintype.card ι := by
  have heps_real : (0 : ℝ) < eps := by exact_mod_cast heps
  have hpwd := hpacking.pairwiseDisjoint_closedBall_half
  have hsub_union : (⋃ x ∈ t, Metric.closedBall x ((eps : ℝ) / 2)) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ ι) (R + (eps : ℝ) / 2) := by
    intro z hz
    obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp hz
    have hx := Metric.mem_closedBall.mp (hsub hxt)
    have hz := Metric.mem_closedBall.mp hzx
    apply Metric.mem_closedBall.mpr
    calc
      dist z 0 ≤ dist z x + dist x 0 := dist_triangle _ _ _
      _ ≤ (eps : ℝ) / 2 + R := add_le_add hz hx
      _ = R + (eps : ℝ) / 2 := by ring
  have hvol_eq : MeasureTheory.volume (⋃ x ∈ t, Metric.closedBall x ((eps : ℝ) / 2)) =
      ∑ x ∈ t, MeasureTheory.volume (Metric.closedBall x ((eps : ℝ) / 2)) :=
    measure_biUnion_finset hpwd (fun _ _ => measurableSet_closedBall)
  have hvol_le : MeasureTheory.volume (⋃ x ∈ t, Metric.closedBall x ((eps : ℝ) / 2)) ≤
      MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ ι) (R + (eps : ℝ) / 2)) :=
    MeasureTheory.measure_mono hsub_union
  have heps_half_pos : 0 < (eps : ℝ) / 2 := by linarith
  have heps_half_nonneg : 0 ≤ (eps : ℝ) / 2 := le_of_lt heps_half_pos
  have hR_plus_pos : 0 ≤ R + (eps : ℝ) / 2 := by linarith
  have hvol_small : ∀ x : EuclideanSpace ℝ ι, MeasureTheory.volume (Metric.closedBall x ((eps : ℝ) / 2)) =
      ENNReal.ofReal (((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) :=
    fun x => volume_closedBall_eq_pow_mul_factor x ((eps : ℝ) / 2) heps_half_nonneg
  have hvol_large : MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ ι) (R + (eps : ℝ) / 2)) =
      ENNReal.ofReal ((R + (eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) :=
    volume_closedBall_eq_pow_mul_factor 0 (R + (eps : ℝ) / 2) hR_plus_pos
  have hvol_sum : ∑ x ∈ t, MeasureTheory.volume (Metric.closedBall x ((eps : ℝ) / 2)) =
      t.card * ENNReal.ofReal (((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) := by
    simp only [hvol_small]
    rw [sum_const]
    simp only [nsmul_eq_mul]
  rw [hvol_eq, hvol_sum] at hvol_le
  rw [hvol_large] at hvol_le
  have hconst_pos := ballVolumeFactor_pos (Fintype.card ι)
  have hsmall_pos : 0 < ((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι) :=
    mul_pos (pow_pos heps_half_pos _) hconst_pos
  have hlarge_pos : 0 < (R + (eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι) :=
    mul_pos (pow_pos (by linarith : 0 < R + (eps : ℝ) / 2) _) hconst_pos
  have hlarge_nonneg : 0 ≤ (R + (eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι) :=
    le_of_lt hlarge_pos
  have h : t.card * ENNReal.ofReal (((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) ≤
      ENNReal.ofReal ((R + (eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) := hvol_le
  rw [← ENNReal.ofReal_natCast] at h
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
  have h' := ENNReal.ofReal_le_ofReal_iff hlarge_nonneg |>.mp h
  have hdiv : t.card * (((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) ≤
      (R + (eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι) := h'
  have hcancel : (t.card : ℝ) ≤ (R + (eps : ℝ) / 2) ^ Fintype.card ι / ((eps : ℝ) / 2) ^ Fintype.card ι := by
    have hne : ((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι) ≠ 0 :=
      ne_of_gt hsmall_pos
    have hsmall_nonneg : 0 ≤ ((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι) :=
      le_of_lt hsmall_pos
    calc (t.card : ℝ)
      _ = t.card * (((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) /
          (((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) := by
        rw [mul_div_cancel_right₀ _ hne]
      _ ≤ (R + (eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι) /
          (((eps : ℝ) / 2) ^ Fintype.card ι * ballVolumeFactor (Fintype.card ι)) := by
        apply div_le_div_of_nonneg_right hdiv hsmall_nonneg
      _ = (R + (eps : ℝ) / 2) ^ Fintype.card ι / ((eps : ℝ) / 2) ^ Fintype.card ι := by
        rw [mul_div_mul_right _ _ (ne_of_gt hconst_pos)]
  have hdiv_eq : (R + (eps : ℝ) / 2) ^ Fintype.card ι / ((eps : ℝ) / 2) ^ Fintype.card ι =
      ((R + (eps : ℝ) / 2) / ((eps : ℝ) / 2)) ^ Fintype.card ι := by
    rw [← div_pow]
  rw [hdiv_eq] at hcancel
  exact hcancel

/-- Main bound: For a packing, |t| ≤ (1 + 2R/ε)^d. -/
private theorem finset_card_le_of_isSeparated_pos
    {t : Finset (EuclideanSpace ℝ ι)} {R : ℝ} {eps : ℝ≥0}
    (hR : 0 ≤ R) (heps : 0 < eps)
    (hsub : (t : Set (EuclideanSpace ℝ ι)) ⊆ Metric.closedBall 0 R)
    (hpacking : Metric.IsSeparated (eps : ℝ≥0∞) (t : Set (EuclideanSpace ℝ ι))) :
    (t.card : ℝ) ≤ (1 + 2 * R / (eps : ℝ)) ^ Fintype.card ι := by
  have h := finset_card_le_radius_ratio hR heps hsub hpacking
  have heq : (R + (eps : ℝ) / 2) / ((eps : ℝ) / 2) = 1 + 2 * R / (eps : ℝ) := by
    field_simp
    ring
  rw [heq] at h
  exact h


end PositiveDimension

/-- Volumetric packing bound including dimension zero. The finite set may be any
strictly separated subset of the closed ball; it need not fill that ball. -/
theorem finset_card_le_of_isSeparated {ι : Type*} [Fintype ι]
    {t : Finset (EuclideanSpace ℝ ι)} {R : ℝ} {ε : ℝ≥0}
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hsub : (t : Set (EuclideanSpace ℝ ι)) ⊆ Metric.closedBall 0 R)
    (hsep : Metric.IsSeparated (ε : ℝ≥0∞) (t : Set (EuclideanSpace ℝ ι))) :
    (t.card : ℝ) ≤ (1 + 2 * R / (ε : ℝ)) ^ Fintype.card ι := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    have hcard : t.card ≤ 1 := Finset.card_le_one.mpr (fun _ _ _ _ => Subsingleton.elim _ _)
    simpa using (Nat.cast_le.mpr hcard : (t.card : ℝ) ≤ (1 : ℕ))
  | inr h =>
    letI := h
    exact finset_card_le_of_isSeparated_pos hR hε hsub hsep

end EuclideanSpace

end
