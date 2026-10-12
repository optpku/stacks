/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap87.Example_87_13_2_RationalExponentSeries

/-!
# Finite-support nonnegative rational-exponent polynomials

The source ring `⋃ n, κ[t^{1/n}]`, realized as the finite-support subring of
`HahnSeries ℚ≥0 κ`, together with its comparison to the `t`-adic series ring
of Example 87.13.2.
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
  add_mem' := sorry
  zero_mem' := sorry
  mul_mem' := sorry
  one_mem' := sorry
  neg_mem' := sorry

namespace RationalExponentPolynomial

/-- Membership in `RationalExponentPolynomial κ` is finiteness of support. -/
theorem mem_iff {κ : Type u} [CommRing κ] {f : HahnSeries ℚ≥0 κ} :
    f ∈ RationalExponentPolynomial κ ↔ f.support.Finite :=
  sorry

/-- The monomial `t` of exponent `1`. -/
def t (κ : Type u) [CommRing κ] : RationalExponentPolynomial κ :=
  ⟨HahnSeries.single (1 : ℚ≥0) 1, sorry⟩

/-- The monomial `t` lies in the rational-exponent polynomial ring. -/
theorem t_mem (κ : Type u) [CommRing κ] :
    HahnSeries.single (1 : ℚ≥0) 1 ∈ RationalExponentPolynomial κ :=
  sorry

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

/-- The inclusion of the polynomial ring into the series ring of Example
87.13.2. -/
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
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The constant-term map is a retraction of `ofConstant`. -/
theorem constantCoeff_comp_ofConstant (κ : Type u) [CommRing κ] :
    (constantCoeff κ).comp (ofConstant κ) = RingHom.id κ :=
  sorry

/-- The rational-exponent polynomial ring over a field is a domain. -/
instance instIsDomain (κ : Type u) [Field κ] :
    IsDomain (RationalExponentPolynomial κ) :=
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

/-- The canonical comparison from the `t`-adic completion of the polynomial
ring to the series ring of Example 87.13.2. -/
def toAdicSeries (κ : Type u) [Field κ] :
    AdicCompletion (Ideal.span {t κ}) (RationalExponentPolynomial κ) →+*
      RationalExponentSeries κ :=
  IsAdicComplete.liftRingHom (Ideal.span {RationalExponentSeries.t κ})
    (toAdicSeriesFamily κ) (toAdicSeries_family_compat κ)

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

end RationalExponentPolynomial
