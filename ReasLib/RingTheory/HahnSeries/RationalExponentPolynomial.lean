/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.Valuation.RationalExponentSeries
public import ReasLib.RingTheory.AdicCompletion.Cofinal

/-!
# Finite-support nonnegative rational-exponent polynomials

The union `⋃ n, κ[t^{1/n}]`, realized as the finite-support subring of
`HahnSeries ℚ≥0 κ`, and its canonical maps to rational-exponent series
and adic completions.
-/

@[expose] public section

noncomputable section

universe u

open HahnSeries

/-- The ring of nonnegative rational-exponent polynomials with coefficients in
`κ`, i.e. Hahn series whose support is finite. -/
def RationalExponentPolynomial (κ : Type u) [CommRing κ] :
    Subring (HahnSeries ℚ≥0 κ) where
  carrier := {f | f.support.Finite}
  add_mem' := by
    intro left right leftFinite rightFinite
    exact (leftFinite.union rightFinite).subset (HahnSeries.support_add_subset left right)
  zero_mem' := by
    simp
  mul_mem' := by
    intro left right leftFinite rightFinite
    exact (leftFinite.image2 (· + ·) rightFinite).subset HahnSeries.support_mul_subset
  one_mem' := by
    exact (Set.finite_singleton (0 : ℚ≥0)).subset HahnSeries.support_single_subset
  neg_mem' := by
    intro series seriesFinite
    exact seriesFinite.subset (HahnSeries.support_neg_subset series)

namespace RationalExponentPolynomial

/-- Membership in `RationalExponentPolynomial κ` is finiteness of support. -/
theorem mem_iff {κ : Type u} [CommRing κ] {f : HahnSeries ℚ≥0 κ} :
    f ∈ RationalExponentPolynomial κ ↔ f.support.Finite :=
  sorry

/-- The monomial `t` lies in the rational-exponent polynomial ring. -/
theorem t_mem (κ : Type u) [CommRing κ] :
    HahnSeries.single (1 : ℚ≥0) 1 ∈ RationalExponentPolynomial κ := by
  exact (Set.finite_singleton (1 : ℚ≥0)).subset HahnSeries.support_single_subset

/-- The monomial `t` of exponent `1`. -/
def t (κ : Type u) [CommRing κ] : RationalExponentPolynomial κ :=
  ⟨HahnSeries.single (1 : ℚ≥0) 1, t_mem κ⟩

/-- Polynomials in `κ` evaluate at `t^{1/n}` into the finite-support subring. -/
theorem ofPolynomial_mem (κ : Type u) [CommRing κ] (n : ℕ+) (p : Polynomial κ) :
    Polynomial.aeval (HahnSeries.single ((n : ℕ) : ℚ≥0)⁻¹ (1 : κ)) p ∈
      RationalExponentPolynomial κ :=
  sorry

/-- The canonical map `κ[X] →+* RationalExponentPolynomial κ` sending `X` to
the monomial `t^{1/n}`. -/
def ofPolynomial (κ : Type u) [CommRing κ] (n : ℕ+) :
    Polynomial κ →+* RationalExponentPolynomial κ :=
  (Polynomial.aeval (HahnSeries.single ((n : ℕ) : ℚ≥0)⁻¹ (1 : κ))).toRingHom.codRestrict
    (RationalExponentPolynomial κ) (ofPolynomial_mem κ n)

/-- `ofPolynomial κ n` sends `X` to the monomial of exponent `1/n`. -/
theorem ofPolynomial_apply_X (κ : Type u) [CommRing κ] (n : ℕ+) :
    (ofPolynomial κ n Polynomial.X : HahnSeries ℚ≥0 κ) =
      HahnSeries.single ((n : ℕ) : ℚ≥0)⁻¹ 1 :=
  sorry

/-- Constants of `κ` embed as finite-support Hahn series. -/
theorem ofConstant_mem (κ : Type u) [CommRing κ] (a : κ) :
    HahnSeries.C a ∈ RationalExponentPolynomial κ :=
  sorry

/-- The canonical map sending a coefficient to the corresponding constant polynomial. -/
def ofConstant (κ : Type u) [CommRing κ] :
    κ →+* RationalExponentPolynomial κ :=
  HahnSeries.C.codRestrict (RationalExponentPolynomial κ) (ofConstant_mem κ)

/-- As a subset of Hahn series, the polynomial ring is the union of the images
of `ofPolynomial κ n`. -/
theorem iUnion_range_ofPolynomial (κ : Type u) [CommRing κ] :
    (RationalExponentPolynomial κ : Set (HahnSeries ℚ≥0 κ)) =
      ⋃ n : ℕ+,
        Set.range
          ((Subring.subtype (RationalExponentPolynomial κ)).comp (ofPolynomial κ n)) :=
  sorry

/-- Finite support implies the initial-interval support condition of
`RationalExponentSeries`. -/
theorem le_rationalExponentSeries (κ : Type u) [CommRing κ] :
    RationalExponentPolynomial κ ≤ RationalExponentSeries κ :=
  sorry

/-- The inclusion of finite-support polynomials into rational-exponent series. -/
def toSeries (κ : Type u) [CommRing κ] :
    RationalExponentPolynomial κ →+* RationalExponentSeries κ :=
  Subring.inclusion (le_rationalExponentSeries κ)

/-- `toSeries` is the subring inclusion into Hahn series. -/
theorem toSeries_apply (κ : Type u) [CommRing κ]
    (f : RationalExponentPolynomial κ) :
    (toSeries κ f : HahnSeries ℚ≥0 κ) = f :=
  sorry

/-- The constant-term map on the rational-exponent polynomial ring. -/
def constantCoeff (κ : Type u) [CommRing κ] :
    RationalExponentPolynomial κ →+* κ where
  toFun f := (f : HahnSeries ℚ≥0 κ).coeff 0
  map_one' := by
    exact HahnSeries.coeff_single_same 0 1
  map_mul' := by
    intro left right
    change ((left : HahnSeries ℚ≥0 κ) * (right : HahnSeries ℚ≥0 κ)).coeff 0 =
      (left : HahnSeries ℚ≥0 κ).coeff 0 * (right : HahnSeries ℚ≥0 κ).coeff 0
    classical
    rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_single (0, 0)
    · intro exponents membership different
      have sum_zero := (Finset.mem_antidiagonal.mp membership).2.2
      obtain ⟨first_zero, second_zero⟩ := add_eq_zero.mp sum_zero
      exact False.elim (different (Prod.ext first_zero second_zero))
    · intro absent
      by_cases left_zero : (left : HahnSeries ℚ≥0 κ).coeff 0 = 0
      · simp [left_zero]
      by_cases right_zero : (right : HahnSeries ℚ≥0 κ).coeff 0 = 0
      · simp [right_zero]
      exact False.elim (absent (Finset.mem_antidiagonal.mpr
        ⟨left_zero, right_zero, zero_add 0⟩))
  map_zero' := by
    rfl
  map_add' := by
    intro left right
    rfl

/-- The constant-term map is a retraction of `ofConstant`. -/
theorem constantCoeff_comp_ofConstant (κ : Type u) [CommRing κ] :
    (constantCoeff κ).comp (ofConstant κ) = RingHom.id κ :=
  sorry

/-- The polynomial ring is Hausdorff for the `t`-adic filtration. -/
instance instIsHausdorff_span_t (κ : Type u) [Field κ] :
    IsHausdorff (Ideal.span {t κ}) (RationalExponentPolynomial κ) :=
  sorry

/-- `toSeries` sends `(t)^n` into `(t)^n` on the series ring. -/
theorem le_comap_pow_span_t (κ : Type u) [CommRing κ] (n : ℕ) :
    (Ideal.span {t κ}) ^ n ≤
      ((Ideal.span {RationalExponentSeries.t κ}) ^ n).comap (toSeries κ) :=
  sorry

/-- Stagewise maps from the `t`-adic completion of the polynomial ring to the
quotients of the series ring. -/
def toAdicSeriesFamily (κ : Type u) [Field κ] (n : ℕ) :
    AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ) →+*
      RationalExponentSeries κ ⧸ (Ideal.span {RationalExponentSeries.t κ}) ^ n :=
  (Ideal.quotientMap ((Ideal.span {RationalExponentSeries.t κ}) ^ n) (toSeries κ)
      (le_comap_pow_span_t κ n)).comp
    (AdicCompletion.evalₐ (Ideal.span {t κ}) n).toRingHom

/-- The family `toAdicSeriesFamily` is compatible with the inverse-limit
transition maps of the `t`-adic series ring. -/
theorem toAdicSeries_family_compat (κ : Type u) [Field κ] {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {RationalExponentSeries.t κ}) hle).comp
        (toAdicSeriesFamily κ n) =
      toAdicSeriesFamily κ m :=
  sorry

/-- Polynomials congruent modulo `(t)^n` have the same coefficients at exponents
strictly less than `n`. -/
theorem coeff_eq_of_sub_mem_span_t_pow (κ : Type u) [CommRing κ]
    (p r : RationalExponentPolynomial κ) (n : ℕ) (q : ℚ≥0) (hq : q < n)
    (hpr : p - r ∈ (Ideal.span {t κ}) ^ n) :
    (p : HahnSeries ℚ≥0 κ).coeff q = (r : HahnSeries ℚ≥0 κ).coeff q :=
  sorry

/-- The coefficient at an exponent below `n` of a polynomial modulo `(t)^n`. -/
def coeffModPow (κ : Type u) [CommRing κ] (n : ℕ) (q : ℚ≥0) (hq : q < n)
    (x : RationalExponentPolynomial κ ⧸ (Ideal.span {t κ}) ^ n) : κ :=
  Quotient.liftOn' x (fun p => (p : HahnSeries ℚ≥0 κ).coeff q) (by
    intro p r hpr
    exact coeff_eq_of_sub_mem_span_t_pow κ p r n q hq
      (Ideal.Quotient.eq.mp (Quotient.sound' hpr)))

/-- On the class of a polynomial, the quotient coefficient is its coefficient. -/
theorem coeffModPow_mk (κ : Type u) [CommRing κ] (n : ℕ) (q : ℚ≥0)
    (hq : q < n) (p : RationalExponentPolynomial κ) :
    coeffModPow κ n q hq (Ideal.Quotient.mk ((Ideal.span {t κ}) ^ n) p) =
      (p : HahnSeries ℚ≥0 κ).coeff q := by
  rfl

/-- The coefficient of a `t`-adic completion element at exponent `q`, computed
from its quotient coordinate numbered `q.num + 1`. -/
def completionCoeff (κ : Type u) [CommRing κ]
    (x : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ))
    (q : ℚ≥0) : κ :=
  coeffModPow κ (q.num + 1) q (by
    have hden : (1 : ℚ≥0) ≤ q.den := by
      exact_mod_cast (Nat.succ_le_iff.mpr q.den_pos)
    calc
      q = q * 1 := (mul_one q).symm
      _ ≤ q * (q.den : ℚ≥0) := mul_le_mul_of_nonneg_left hden (zero_le : 0 ≤ q)
      _ = q.num := q.mul_den_eq_num
      _ < ((q.num + 1 : ℕ) : ℚ≥0) := by exact_mod_cast Nat.lt_succ_self q.num)
    (AdicCompletion.evalₐ (Ideal.span {t κ}) (q.num + 1) x)

/-- A completion coefficient can be computed at any quotient coordinate whose
index exceeds its exponent. -/
theorem completionCoeff_eq_coeffModPow (κ : Type u) [CommRing κ]
    (x : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ))
    (n : ℕ) (q : ℚ≥0) (hq : q < n) :
    completionCoeff κ x q =
      coeffModPow κ n q hq (AdicCompletion.evalₐ (Ideal.span {t κ}) n x) :=
  sorry

-- These one-use assembly facts stay private. The compatibility option lets
-- the exposed ring homomorphism use them without publishing additional API.
set_option backward.privateInPublic true in
private theorem completionCoeff_support_finite (κ : Type u) [Field κ]
    (x : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ))
    (n : ℕ) :
    (Function.support (completionCoeff κ x) ∩ Set.Iic (n : ℚ≥0)).Finite :=
  sorry

set_option backward.privateInPublic true in
private theorem completionCoeff_support_isPWO (κ : Type u) [Field κ]
    (x : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ)) :
    (Function.support (completionCoeff κ x)).IsPWO :=
  sorry

set_option backward.privateInPublic true in
private def completionHahn (κ : Type u) [Field κ]
    (x : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ)) :
    HahnSeries ℚ≥0 κ where
  coeff := completionCoeff κ x
  isPWO_support' := completionCoeff_support_isPWO κ x

set_option backward.privateInPublic true in
private theorem completionHahn_map_zero (κ : Type u) [Field κ] :
    completionHahn κ 0 = 0 :=
  sorry

set_option backward.privateInPublic true in
private theorem completionHahn_map_one (κ : Type u) [Field κ] :
    completionHahn κ 1 = 1 :=
  sorry

set_option backward.privateInPublic true in
private theorem completionHahn_map_add (κ : Type u) [Field κ]
    (x y : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ)) :
    completionHahn κ (x + y) = completionHahn κ x + completionHahn κ y :=
  sorry

set_option backward.privateInPublic true in
private theorem completionHahn_map_mul (κ : Type u) [Field κ]
    (x y : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ)) :
    completionHahn κ (x * y) = completionHahn κ x * completionHahn κ y :=
  sorry

-- The exposed map uses private coefficient assembly and proof laws so these
-- implementation declarations do not become public API.
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The canonical comparison from the `t`-adic completion of the polynomial
ring to rational-exponent series, reconstructed from quotient coefficients. -/
def toAdicSeries (κ : Type u) [Field κ] :
    AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ) →+*
      RationalExponentSeries κ where
  toFun x := ⟨completionHahn κ x, completionCoeff_support_finite κ x⟩
  map_zero' := Subtype.ext (completionHahn_map_zero κ)
  map_one' := Subtype.ext (completionHahn_map_one κ)
  map_add' x y := Subtype.ext (completionHahn_map_add κ x y)
  map_mul' x y := Subtype.ext (completionHahn_map_mul κ x y)

/-- The coefficients of the canonical completion map are the coefficients
computed from the polynomial quotient coordinates. -/
theorem toAdicSeries_coeff (κ : Type u) [Field κ]
    (x : AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ))
    (q : ℚ≥0) :
    (toAdicSeries κ x : HahnSeries ℚ≥0 κ).coeff q = completionCoeff κ x q := by
  rfl

/-- Reduction of the canonical completion map modulo `(t)^n` is the canonical
stagewise map induced by the polynomial inclusion. -/
theorem toAdicSeries_eval (κ : Type u) [Field κ] (n : ℕ) :
    (Ideal.Quotient.mk ((Ideal.span {RationalExponentSeries.t κ}) ^ n)).comp
        (toAdicSeries κ) = toAdicSeriesFamily κ n :=
  sorry

/-- `toAdicSeries` extends `toSeries` along the canonical map to the `t`-adic
completion. -/
theorem toAdicSeries_comp_of (κ : Type u) [Field κ] :
    (toAdicSeries κ).comp
        (algebraMap (RationalExponentPolynomial κ)
          (AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ))) =
      toSeries κ :=
  sorry

/-- The augmentation ideal consists of polynomials with zero constant term. -/
def augmentationIdeal (κ : Type u) [CommRing κ] : Ideal (RationalExponentPolynomial κ) :=
  RingHom.ker (constantCoeff κ)

/-- Membership in the augmentation ideal is vanishing of the constant term. -/
theorem mem_augmentationIdeal_iff (κ : Type u) [CommRing κ]
    (a : RationalExponentPolynomial κ) :
    a ∈ augmentationIdeal κ ↔ constantCoeff κ a = 0 :=
  sorry

/-- The constant-term map vanishes on its kernel. -/
theorem constantCoeff_eq_zero_of_mem_augmentationIdeal (κ : Type u) [Field κ]
    (a : RationalExponentPolynomial κ) (ha : a ∈ augmentationIdeal κ) :
    constantCoeff κ a = 0 :=
  sorry

/-- The augmentation ideal is a maximal ideal when `κ` is a field. -/
instance instIsMaximal (κ : Type u) [Field κ] :
    (augmentationIdeal κ).IsMaximal :=
  sorry

/-- The residue map of the augmentation-adic completion, sending a compatible family
to the constant term of its first coordinate. -/
def constantCoeffResidue (κ : Type u) [Field κ] :
    AdicCompletion (augmentationIdeal κ)
      (RationalExponentPolynomial κ) →+* κ :=
  (Ideal.Quotient.lift (augmentationIdeal κ)
      (constantCoeff κ) (constantCoeff_eq_zero_of_mem_augmentationIdeal κ)).comp
    (AdicCompletion.evalOneₐ (augmentationIdeal κ)).toRingHom

/-- The finite-support polynomial union is not a local ring. -/
theorem not_isLocalRing (κ : Type u) [Field κ] :
    ¬ IsLocalRing (RationalExponentPolynomial κ) :=
  sorry

/-- The finite-support polynomial union is not a valuation ring. -/
theorem not_valuationRing (κ : Type u) [Field κ] :
    ¬ ValuationRing (RationalExponentPolynomial κ) :=
  sorry

/-- The canonical comparison from the principal-adic completion to the
radical-adic completion of the rational-exponent polynomial ring is not bijective. -/
theorem not_bijective_mapOfRadical (κ : Type u) [Field κ] :
    ¬ Function.Bijective
      (AdicCompletion.comparisonRingHomOfPowLe
        (Ideal.span {t κ}) (Ideal.span {t κ}).radical 1
        (by simpa only [pow_one] using (Ideal.span {t κ}).le_radical)) :=
  sorry

/-- The radical of the ideal generated by the exponent-one monomial is the
augmentation ideal. -/
theorem radical_span_t_eq_augmentationIdeal (κ : Type u) [Field κ] :
    (Ideal.span {t κ}).radical = augmentationIdeal κ :=
  sorry

/-- The augmentation ideal of the rational-exponent polynomial ring is idempotent. -/
theorem augmentationIdeal_sq_eq (κ : Type u) [Field κ] :
    augmentationIdeal κ ^ 2 = augmentationIdeal κ :=
  sorry

/-- The canonical constant-term residue map identifies the augmentation-adic
completion with the coefficient field. -/
theorem bijective_constantCoeffResidue (κ : Type u) [Field κ] :
    Function.Bijective (constantCoeffResidue κ) :=
  sorry

/-- The canonical map from the principal-adic completion to rational-exponent
series is bijective. -/
theorem toAdicSeries_bijective (κ : Type u) [Field κ] :
    Function.Bijective (toAdicSeries κ) :=
  sorry

/-- The canonical map from rational-exponent polynomials to their completion
at the exponent-one monomial is injective. -/
theorem of_span_t_injective (κ : Type u) [Field κ] :
    Function.Injective
      (AdicCompletion.of (Ideal.span {t κ}) (RationalExponentPolynomial κ)) :=
  sorry

end RationalExponentPolynomial
