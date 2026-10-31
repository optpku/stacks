/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The affine curve `t ^ 2 = s ^ 5 + 8` in `Fin 2 → ℂ`

Classical `ℂ`-points of the plane curve `X` given by `t ^ 2 = s ^ 5 + 8`, the
point `x = (1, 3)`, the punctured open `U = X \ {x}`, and the extra regular
function on `U` which is not the restriction of a polynomial in `s` and `t`.
Here `s` is `X 0` and `t` is `X 1`.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial.AffineTsqS5p8

/-- The equation `t ^ 2 - s ^ 5 - 8` of the affine plane curve, with `X 0`
corresponding to `s` and `X 1` corresponding to `t`. -/
def equation : MvPolynomial (Fin 2) ℂ :=
  X 1 ^ 2 - X 0 ^ 5 - 8

/-- The defining equation is `X 1 ^ 2 - X 0 ^ 5 - 8`. -/
theorem equation_eq : equation = X 1 ^ 2 - X 0 ^ 5 - 8 :=
  rfl

/-- The affine plane curve `X` cut out by `t ^ 2 = s ^ 5 + 8` in `Fin 2 → ℂ`. -/
def curve : Set (Fin 2 → ℂ) :=
  zeroLocus ℂ (Ideal.span {equation})

/-- A point lies on `curve` if and only if the defining equation vanishes. -/
theorem mem_curve_iff (p : Fin 2 → ℂ) : p ∈ curve ↔ eval p equation = 0 :=
  by
    simp only [curve, mem_zeroLocus_iff]
    constructor
    · intro h
      exact h equation (Ideal.subset_span (Set.mem_singleton equation))
    · intro h f hf
      rw [Ideal.mem_span_singleton'] at hf
      obtain ⟨q, hq⟩ := hf
      simpa [← hq, h]

/-- The point `x = (1, 3)` on the curve, with `s`-coordinate `1` and
`t`-coordinate `3`. -/
def point : Fin 2 → ℂ := fun i ↦ if i = 0 then 1 else 3

/-- The distinguished point has `s`-coordinate `1` and `t`-coordinate `3`. -/
theorem point_eq : point 0 = 1 ∧ point 1 = 3 :=
  by norm_num [point]

/-- The point `(1, 3)` lies on the curve. -/
theorem point_mem_curve : point ∈ curve :=
  by
    rw [mem_curve_iff]
    norm_num [equation, point]

/-- The Zariski open `U = X \ {x}` obtained by removing the point `(1, 3)`. -/
def punctured : Set (Fin 2 → ℂ) :=
  curve \ {point}

/-- The punctured curve is the complement of the singleton `{point}` in `curve`. -/
theorem punctured_eq : punctured = curve \ {point} :=
  rfl

/-- The numerator `t + 3` of the standard ratio presentation on `s ≠ 1`. -/
def tAddThree : MvPolynomial (Fin 2) ℂ :=
  X 1 + 3

/-- `tAddThree` is the polynomial `X 1 + 3`. -/
theorem tAddThree_eq : tAddThree = X 1 + 3 :=
  rfl

/-- The denominator `s - 1` of the standard ratio presentation on `s ≠ 1`. -/
def sSubOne : MvPolynomial (Fin 2) ℂ :=
  X 0 - 1

/-- `sSubOne` is the polynomial `X 0 - 1`. -/
theorem sSubOne_eq : sSubOne = X 0 - 1 :=
  rfl

/-- The geometric sum `s ^ 4 + s ^ 3 + s ^ 2 + s + 1` appearing in the
identity `(t - 3)(t + 3) = (s - 1)(s ^ 4 + s ^ 3 + s ^ 2 + s + 1)`. -/
def sGeomSum : MvPolynomial (Fin 2) ℂ :=
  X 0 ^ 4 + X 0 ^ 3 + X 0 ^ 2 + X 0 + 1

/-- `sGeomSum` is the polynomial `X 0 ^ 4 + X 0 ^ 3 + X 0 ^ 2 + X 0 + 1`. -/
theorem sGeomSum_eq : sGeomSum = X 0 ^ 4 + X 0 ^ 3 + X 0 ^ 2 + X 0 + 1 :=
  rfl

/-- The denominator `t - 3` of the residual ratio presentation on `s = 1`. -/
def tSubThree : MvPolynomial (Fin 2) ℂ :=
  X 1 - 3

/-- `tSubThree` is the polynomial `X 1 - 3`. -/
theorem tSubThree_eq : tSubThree = X 1 - 3 :=
  rfl

/-- The extra function on `punctured`, given by `(t + 3) / (s - 1)` away from
`s = 1` and by `(s ^ 4 + s ^ 3 + s ^ 2 + s + 1) / (t - 3)` on the residual
locus `s = 1`. -/
def extraFunction : punctured → ℂ := fun z ↦
  if z.val 0 = 1 then
    eval z.val sGeomSum / eval z.val tSubThree
  else
    eval z.val tAddThree / eval z.val sSubOne

/-- Away from `s = 1`, `extraFunction` is the ratio `(t + 3) / (s - 1)`. -/
theorem extraFunction_eq_of_s_ne_one (z : punctured) (hs : z.val 0 ≠ 1) :
    extraFunction z = eval z.val tAddThree / eval z.val sSubOne :=
  by simp [extraFunction, hs]

/-- On the residual locus `s = 1` in `punctured`, `extraFunction` is the ratio
`(s ^ 4 + s ^ 3 + s ^ 2 + s + 1) / (t - 3)`. -/
theorem extraFunction_eq_of_s_eq_one (z : punctured) (hs : z.val 0 = 1) :
    extraFunction z = eval z.val sGeomSum / eval z.val tSubThree :=
  by simp [extraFunction, hs]

private theorem ratio_identity (p : Fin 2 → ℂ) (hp : p ∈ curve) :
    eval p tAddThree * eval p tSubThree = eval p sGeomSum * eval p sSubOne := by
  have h : p 1 ^ 2 - p 0 ^ 5 - 8 = 0 := by
    simpa [equation] using (mem_curve_iff p).mp hp
  apply sub_eq_zero.mp
  calc
    eval p tAddThree * eval p tSubThree - eval p sGeomSum * eval p sSubOne =
        p 1 ^ 2 - p 0 ^ 5 - 8 := by
      simp [tAddThree, tSubThree, sGeomSum, sSubOne]
      ring
    _ = 0 := h

private theorem extraFunction_eq_of_t_ne_three (z : punctured) (ht : z.val 1 ≠ 3) :
    extraFunction z = eval z.val sGeomSum / eval z.val tSubThree := by
  by_cases hs : z.val 0 = 1
  · exact extraFunction_eq_of_s_eq_one z hs
  · rw [extraFunction_eq_of_s_ne_one z hs]
    apply (div_eq_div_iff (by simpa [sSubOne] using sub_ne_zero.mpr hs)
      (by simpa [tSubThree] using sub_ne_zero.mpr ht)).mpr
    exact ratio_identity z.val z.property.1

/-- `extraFunction` is regular on `punctured`. -/
theorem isRegular_extraFunction : IsRegular extraFunction :=
  by
    intro z
    by_cases hs : z.val 0 = 1
    · have ht : z.val 1 ≠ 3 := by
        intro ht
        apply z.property.2
        apply Set.mem_singleton_iff.mpr
        funext i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · simpa [point] using hs
        · simpa [point] using ht
      refine ⟨punctured \ zeroLocus ℂ (Ideal.span {tSubThree}),
        ⟨Set.sdiff_subset, Ideal.span {tSubThree}, rfl⟩, ?_, sGeomSum, tSubThree, ?_, ?_⟩
      · exact ⟨z.property, by simpa [zeroLocus_span, tSubThree, sub_eq_zero] using ht⟩
      · intro u hu
        simpa [zeroLocus_span] using hu.2
      · intro u hu
        apply extraFunction_eq_of_t_ne_three
        simpa [zeroLocus_span, tSubThree, sub_eq_zero] using hu.2
    · refine ⟨punctured \ zeroLocus ℂ (Ideal.span {sSubOne}),
        ⟨Set.sdiff_subset, Ideal.span {sSubOne}, rfl⟩, ?_, tAddThree, sSubOne, ?_, ?_⟩
      · exact ⟨z.property, by simpa [zeroLocus_span, sSubOne, sub_eq_zero] using hs⟩
      · intro u hu
        simpa [zeroLocus_span] using hu.2
      · intro u hu
        apply extraFunction_eq_of_s_ne_one
        simpa [zeroLocus_span, sSubOne, sub_eq_zero] using hu.2

/-- A polynomial relation holding where `s ≠ 1` also holds at the removed point. -/
private theorem eval_point_eq_zero_of_vanishes (q : MvPolynomial (Fin 2) ℂ)
    (hq : ∀ x ∈ curve, x 0 ≠ 1 → eval x q = 0) : eval point q = 0 := by
  -- Multiplication by `s - 1` gives vanishing on the whole curve.
  have hv : sSubOne * q ∈ vanishingIdeal ℂ curve := by
    intro x hx
    change eval x (sSubOne * q) = 0
    by_cases hs : x 0 = 1
    · simp [sSubOne, hs]
    · simp only [map_mul, hq x hx hs, mul_zero]
  have hr : sSubOne * q ∈ (Ideal.span {equation}).radical := by
    simpa only [curve, vanishingIdeal_zeroLocus_eq_radical] using hv
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hr
  have hd : equation ∣ (sSubOne * q) ^ n := Ideal.mem_span_singleton.mp hn
  -- Translate `s - 1` to a variable and cancel its powers from the divisibility relation.
  let shift : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
    aeval fun i ↦ X i + C (if i = 0 then 1 else 0)
  have hs : shift sSubOne = X 0 := by simp [shift, sSubOne]
  have heq : shift equation = X 1 ^ 2 - (X 0 + 1) ^ 5 - 8 := by
    simp only [equation, map_sub, map_pow, map_ofNat]
    simp [shift]
  have hf : ¬ (X 0 : MvPolynomial (Fin 2) ℂ) ∣ shift equation := by
    rintro ⟨r, hr⟩
    have h := congrArg (eval (fun _ ↦ (0 : ℂ))) hr
    simp only [heq, map_sub, map_pow, map_add, map_one, map_ofNat, map_mul, eval_X] at h
    norm_num at h
  have cancel : ∀ (m : ℕ) (r : MvPolynomial (Fin 2) ℂ),
      shift equation ∣ X 0 ^ m * r → shift equation ∣ r := by
    intro m
    induction m with
    | zero =>
      intro r hr
      simpa using hr
    | succ m ih =>
      intro r hr
      rw [pow_succ', mul_assoc] at hr
      rcases dvd_X_mul_iff.mp hr with hr | ⟨hr, _⟩
      · exact ih r hr
      · exact (hf hr).elim
  have hshift : shift equation ∣ X 0 ^ n * (shift q) ^ n := by
    simpa only [map_pow, map_mul, hs, mul_pow] using map_dvd shift hd
  obtain ⟨r, hr⟩ := cancel n ((shift q) ^ n) hshift
  let y : Fin 2 → ℂ := fun i ↦ if i = 0 then 0 else 3
  have heval : eval y (shift q) = eval point q := by
    change eval y (eval₂ C _ q) = _
    rw [← eval_assoc]
    congr 2
    funext i
    by_cases hi : i = 0 <;> simp [y, point, hi]
  have hzero : eval y (shift equation) = 0 := by norm_num [y, heq]
  have h := congrArg (eval y) hr
  rw [map_pow, map_mul, heval, hzero, zero_mul] at h
  exact eq_zero_of_pow_eq_zero h

/-- `extraFunction` is not given by a polynomial in `s` and `t`. -/
theorem not_isPolynomial_extraFunction : ¬ IsPolynomial extraFunction :=
  by
    rintro ⟨p, hp⟩
    let q := sSubOne * p - tAddThree
    have hq : eval point q = 0 := by
      apply eval_point_eq_zero_of_vanishes
      intro x hx hs
      have hxU : x ∈ punctured := by
        refine ⟨hx, ?_⟩
        intro h
        apply hs
        simpa [point] using congrFun (Set.mem_singleton_iff.mp h) 0
      have hd : eval x sSubOne ≠ 0 := by
        simpa [sSubOne] using sub_ne_zero.mpr hs
      have he : eval x tAddThree / eval x sSubOne = eval x p := by
        rw [← extraFunction_eq_of_s_ne_one ⟨x, hxU⟩ hs]
        exact hp ⟨x, hxU⟩
      simpa [q, mul_comm] using (sub_eq_zero.mpr ((div_eq_iff hd).mp he).symm)
    norm_num [q, sSubOne, tAddThree, point] at hq

/-- `extraFunction` is not the restriction of a regular function on all of
`Fin 2 → ℂ`. -/
theorem not_restricts_from_isRegular_univ :
    ¬ ∃ (ψ : ∀ (w : (Set.univ : Set (Fin 2 → ℂ))), ℂ),
      IsRegular ψ ∧ ∀ z : punctured,
        extraFunction z = ψ ⟨z.val, Set.mem_univ z.val⟩ :=
  by
    classical
    rintro ⟨ψ, hψ, hres⟩
    obtain ⟨U, ⟨_, I, hU⟩, hzU, f, g, hg, hfg⟩ := hψ ⟨point, Set.mem_univ point⟩
    have hI : point ∉ zeroLocus ℂ I := by
      rw [hU] at hzU
      exact hzU.2
    simp only [mem_zeroLocus_iff, not_forall] at hI
    obtain ⟨a, haI, hap⟩ := hI
    change eval point a ≠ 0 at hap
    let q := a * (sSubOne * f - tAddThree * g)
    have hq : eval point q = 0 := by
      apply eval_point_eq_zero_of_vanishes
      intro x hx hs
      by_cases ha : eval x a = 0
      · simp [q, ha]
      · have hxU : x ∈ U := by
          rw [hU]
          refine ⟨Set.mem_univ x, ?_⟩
          intro h
          exact ha (h a haI)
        have hxP : x ∈ punctured := by
          refine ⟨hx, ?_⟩
          intro h
          apply hs
          simpa [point] using congrFun (Set.mem_singleton_iff.mp h) 0
        have hd : eval x sSubOne ≠ 0 := by
          simpa [sSubOne] using sub_ne_zero.mpr hs
        have he : eval x tAddThree / eval x sSubOne = eval x f / eval x g := by
          rw [← extraFunction_eq_of_s_ne_one ⟨x, hxP⟩ hs, hres ⟨x, hxP⟩]
          exact hfg ⟨x, Set.mem_univ x⟩ hxU
        have hcross := (div_eq_div_iff hd (hg x hxU)).mp he
        have hdiff : eval x (sSubOne * f - tAddThree * g) = 0 := by
          simp only [map_sub, map_mul]
          exact sub_eq_zero.mpr ((mul_comm _ _).trans hcross.symm)
        simp only [q, map_mul, hdiff, mul_zero]
    apply (mul_ne_zero hap ?_) (by simpa only [q, map_mul] using hq)
    have hgp : eval point g ≠ 0 := hg point hzU
    simpa [sSubOne, tAddThree, point] using
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (6 : ℂ) ≠ 0) hgp))

/-- `extraFunction` is regular on the curve `t ^ 2 = s ^ 5 + 8` with `(1, 3)`
removed, but is not the restriction of a polynomial on the complex affine plane. -/
theorem isRegular_not_isPolynomial_extraFunction :
    IsRegular extraFunction ∧ ¬ IsPolynomial extraFunction :=
  ⟨isRegular_extraFunction, not_isPolynomial_extraFunction⟩

end MvPolynomial.AffineTsqS5p8
