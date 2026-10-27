/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.PhamBrieskorn
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localization of Pham–Brieskorn hypersurfaces

For `t = 1 + e * r * s`, inverting the third coordinate identifies the
Pham–Brieskorn ring with a localization of a polynomial ring in two variables.
-/

@[expose] public section

noncomputable section

universe u

open MvPolynomial

namespace MvPolynomial.PhamBrieskorn

/-- The plane polynomial `X 0 ^ r + X 1 ^ s`. -/
def planeRelation (k : Type u) [CommRing k] (r s : ℕ) : MvPolynomial (Fin 2) k :=
  X 0 ^ r + X 1 ^ s

/-- The localization `k[x', y', 1/z]` modeled as the plane polynomial ring away
from `X 0 ^ r + X 1 ^ s`. -/
abbrev LocalizedPlane (k : Type u) [CommRing k] (r s : ℕ) :=
  Localization.Away (planeRelation k r s)

/-- The localized plane inverts the plane relation. -/
theorem isUnit_algebraMap_planeRelation (k : Type u) [CommRing k] (r s : ℕ) :
    IsUnit (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s)
      (planeRelation k r s)) :=
  IsLocalization.Away.algebraMap_isUnit (planeRelation k r s)

/-- The class of `x' = x * z⁻¹ ^ (e * s)` in `A[1/z]` when `t = 1 + e * r * s`. -/
def x' (k : Type u) [CommRing k] (e r s : ℕ) :
    Localization.Away (z k r s (1 + e * r * s)) :=
  algebraMap (Ring k r s (1 + e * r * s))
      (Localization.Away (z k r s (1 + e * r * s)))
      (x k r s (1 + e * r * s)) *
    IsLocalization.Away.invSelf (z k r s (1 + e * r * s)) ^ (e * s)

/-- The class of `y' = y * z⁻¹ ^ (e * r)` in `A[1/z]` when `t = 1 + e * r * s`. -/
def y' (k : Type u) [CommRing k] (e r s : ℕ) :
    Localization.Away (z k r s (1 + e * r * s)) :=
  algebraMap (Ring k r s (1 + e * r * s))
      (Localization.Away (z k r s (1 + e * r * s)))
      (y k r s (1 + e * r * s)) *
    IsLocalization.Away.invSelf (z k r s (1 + e * r * s)) ^ (e * r)

/-- In `A[1/z]`, the substituted coordinates satisfy `(x') ^ r + (y') ^ s = -z`. -/
theorem x'_pow_add_y'_pow (k : Type u) [CommRing k] (e r s : ℕ) :
    x' k e r s ^ r + y' k e r s ^ s =
      - algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s)))
          (z k r s (1 + e * r * s)) :=
  by
    have hrelation :
        x k r s (1 + e * r * s) ^ r + y k r s (1 + e * r * s) ^ s +
          z k r s (1 + e * r * s) ^ (1 + e * r * s) = 0 := by
      simp only [x, y, z, ← map_pow, ← map_add]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton (relation k r s (1 + e * r * s))))
    have h := congrArg
      (algebraMap (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s)))) hrelation
    simp only [map_add, map_pow, map_zero] at h
    have hinv (n : ℕ) :
        algebraMap (Ring k r s (1 + e * r * s))
            (Localization.Away (z k r s (1 + e * r * s)))
            (z k r s (1 + e * r * s)) ^ n *
          IsLocalization.Away.invSelf (z k r s (1 + e * r * s)) ^ n = 1 := by
      rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
    have hexp : e * s * r = e * r * s := by ac_rfl
    simp only [x', y', mul_pow, ← pow_mul]
    rw [hexp, ← add_mul, eq_neg_of_add_eq_zero_left h, neg_mul, pow_add, pow_one,
      mul_assoc (algebraMap (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s))) (z k r s (1 + e * r * s))),
      hinv, mul_one]

/-- The coordinate substitution `X 0 ↦ x'`, `X 1 ↦ y'` into `A[1/z]`. -/
def planeSubst (k : Type u) [CommRing k] (e r s : ℕ) :
    Fin 2 → Localization.Away (z k r s (1 + e * r * s)) :=
  ![x' k e r s, y' k e r s]

/-- Evaluation of plane polynomials at `(x', y')` in `A[1/z]`. -/
def planeEval (k : Type u) [CommRing k] (e r s : ℕ) :
    MvPolynomial (Fin 2) k →+* Localization.Away (z k r s (1 + e * r * s)) :=
  (aeval (planeSubst k e r s)).toRingHom

/-- Evaluation at `(x', y')` sends the first plane variable to `x'`. -/
theorem planeEval_X_zero (k : Type u) [CommRing k] (e r s : ℕ) :
    planeEval k e r s (X 0) = x' k e r s :=
  by simp [planeEval, planeSubst]

/-- Evaluation at `(x', y')` sends the second plane variable to `y'`. -/
theorem planeEval_X_one (k : Type u) [CommRing k] (e r s : ℕ) :
    planeEval k e r s (X 1) = y' k e r s :=
  by simp [planeEval, planeSubst]

/-- The plane relation becomes a unit in `A[1/z]`, since it is associated to `-z`. -/
theorem isUnit_planeEval_planeRelation (k : Type u) [CommRing k] (e r s : ℕ) :
    IsUnit (planeEval k e r s (planeRelation k r s)) :=
  by
    rw [planeRelation, map_add, map_pow, map_pow, planeEval_X_zero, planeEval_X_one,
      x'_pow_add_y'_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (z k r s (1 + e * r * s))).neg

/-- The induced map `k[x', y', 1/z] → A[1/z]` when `t = 1 + e * r * s`. -/
def ofLocalizedPlane (k : Type u) [CommRing k] (e r s : ℕ) :
    LocalizedPlane k r s →+* Localization.Away (z k r s (1 + e * r * s)) :=
  IsLocalization.Away.lift (planeRelation k r s) (isUnit_planeEval_planeRelation k e r s)

/-- The image of `z` in the localized plane, namely `-(X 0 ^ r + X 1 ^ s)`. -/
def zImage (k : Type u) [CommRing k] (r s : ℕ) : LocalizedPlane k r s :=
  algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (- planeRelation k r s)

/-- The image of `z` is the negation of the inverted plane relation. -/
theorem zImage_neg_planeRelation (k : Type u) [CommRing k] (r s : ℕ) :
    zImage k r s =
      - algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s)
          (planeRelation k r s) :=
  by simp [zImage]

/-- The coordinate substitution sending `x, y, z` to
`x' * z ^ (e * s)`, `y' * z ^ (e * r)`, and `- (x' ^ r + y' ^ s)`. -/
def spaceSubst (k : Type u) [CommRing k] (e r s : ℕ) : Fin 3 → LocalizedPlane k r s :=
  ![algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 0) *
      zImage k r s ^ (e * s),
    algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 1) *
      zImage k r s ^ (e * r),
    zImage k r s]

/-- Evaluation of space polynomials at the special-case substitution into the
localized plane. -/
def spaceEval (k : Type u) [CommRing k] (e r s : ℕ) :
    MvPolynomial (Fin 3) k →+* LocalizedPlane k r s :=
  (aeval (spaceSubst k e r s)).toRingHom

/-- The special-case substitution kills the Pham–Brieskorn relation. -/
theorem spaceEval_relation (k : Type u) [CommRing k] (e r s : ℕ)
    (f : MvPolynomial (Fin 3) k)
    (hf : f ∈ Ideal.span {relation k r s (1 + e * r * s)}) :
    spaceEval k e r s f = 0 :=
  by
    have hrelation : spaceEval k e r s (relation k r s (1 + e * r * s)) = 0 := by
      have hz :
          algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 0) ^ r +
            algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 1) ^ s =
              -zImage k r s := by
        simp [zImage, planeRelation]
      have hexp : e * s * r = e * r * s := by ac_rfl
      simp only [spaceEval, relation, map_add, map_pow, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X]
      change
        (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 0) *
            zImage k r s ^ (e * s)) ^ r +
          (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 1) *
            zImage k r s ^ (e * r)) ^ s +
          zImage k r s ^ (1 + e * r * s) = 0
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, hexp, ← add_mul, hz,
        pow_add, pow_one]
      ring
    have hle : Ideal.span {relation k r s (1 + e * r * s)} ≤
        RingHom.ker (spaceEval k e r s) := by
      apply Ideal.span_le.mpr
      intro g hg
      rcases Set.mem_singleton_iff.mp hg with rfl
      exact hrelation
    exact hle hf

/-- The quotient map `A → k[x', y', 1/z]` when `t = 1 + e * r * s`. -/
def toLocalizedPlaneOnRing (k : Type u) [CommRing k] (e r s : ℕ) :
    Ring k r s (1 + e * r * s) →+* LocalizedPlane k r s :=
  Ideal.Quotient.lift (Ideal.span {relation k r s (1 + e * r * s)})
    (spaceEval k e r s) (spaceEval_relation k e r s)

/-- The image of `z` is a unit in the localized plane. -/
theorem isUnit_toLocalizedPlaneOnRing_z (k : Type u) [CommRing k] (e r s : ℕ) :
    IsUnit (toLocalizedPlaneOnRing k e r s (z k r s (1 + e * r * s))) :=
  by
    have hz : toLocalizedPlaneOnRing k e r s (z k r s (1 + e * r * s)) =
        zImage k r s := by
      simp [toLocalizedPlaneOnRing, z, spaceEval, spaceSubst]
    rw [hz, zImage_neg_planeRelation]
    exact (isUnit_algebraMap_planeRelation k r s).neg

/-- The induced map `A[1/z] → k[x', y', 1/z]` when `t = 1 + e * r * s`. -/
def toLocalizedPlane (k : Type u) [CommRing k] (e r s : ℕ) :
    Localization.Away (z k r s (1 + e * r * s)) →+* LocalizedPlane k r s :=
  IsLocalization.Away.lift (z k r s (1 + e * r * s))
    (isUnit_toLocalizedPlaneOnRing_z k e r s)

private theorem toLocalizedPlane_x' (k : Type u) [CommRing k] (e r s : ℕ) :
    toLocalizedPlane k e r s (x' k e r s) =
      algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 0) := by
  have hz : toLocalizedPlane k e r s
      (algebraMap (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s)))
        (z k r s (1 + e * r * s))) = zImage k r s := by
    simp only [toLocalizedPlane, IsLocalization.Away.lift_eq]
    simp [toLocalizedPlaneOnRing, z, spaceEval, spaceSubst]
  have hinv : zImage k r s *
      toLocalizedPlane k e r s (IsLocalization.Away.invSelf (z k r s (1 + e * r * s))) =
        1 := by
    rw [← hz, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hx : toLocalizedPlane k e r s
      (algebraMap (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s)))
        (x k r s (1 + e * r * s))) =
      algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 0) *
        zImage k r s ^ (e * s) := by
    simp [toLocalizedPlane, toLocalizedPlaneOnRing, x, spaceEval, spaceSubst]
  rw [x', map_mul, map_pow, hx, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]

private theorem toLocalizedPlane_y' (k : Type u) [CommRing k] (e r s : ℕ) :
    toLocalizedPlane k e r s (y' k e r s) =
      algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 1) := by
  have hz : toLocalizedPlane k e r s
      (algebraMap (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s)))
        (z k r s (1 + e * r * s))) = zImage k r s := by
    simp only [toLocalizedPlane, IsLocalization.Away.lift_eq]
    simp [toLocalizedPlaneOnRing, z, spaceEval, spaceSubst]
  have hinv : zImage k r s *
      toLocalizedPlane k e r s (IsLocalization.Away.invSelf (z k r s (1 + e * r * s))) =
        1 := by
    rw [← hz, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hy : toLocalizedPlane k e r s
      (algebraMap (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s)))
        (y k r s (1 + e * r * s))) =
      algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 1) *
        zImage k r s ^ (e * r) := by
    simp [toLocalizedPlane, toLocalizedPlaneOnRing, y, spaceEval, spaceSubst]
  rw [y', map_mul, map_pow, hy, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]

/-- The two special-case maps are inverse on the localized plane. -/
theorem toLocalizedPlane_comp_ofLocalizedPlane (k : Type u) [CommRing k]
    (e r s : ℕ) :
    (toLocalizedPlane k e r s).comp (ofLocalizedPlane k e r s) =
      RingHom.id (LocalizedPlane k r s) :=
  by
    apply IsLocalization.ringHom_ext (Submonoid.powers (planeRelation k r s))
    apply MvPolynomial.ringHom_ext
    · intro c
      change toLocalizedPlane k e r s
          (ofLocalizedPlane k e r s
            (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (C c))) =
        algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (C c)
      simp only [ofLocalizedPlane, IsLocalization.Away.lift_eq, planeEval,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [IsScalarTower.algebraMap_apply k (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s)))]
      change toLocalizedPlane k e r s
          (algebraMap (Ring k r s (1 + e * r * s))
            (Localization.Away (z k r s (1 + e * r * s)))
            (Ideal.Quotient.mk _ (C c))) = _
      simp only [toLocalizedPlane, IsLocalization.Away.lift_eq, toLocalizedPlaneOnRing,
        Ideal.Quotient.lift_mk, spaceEval, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) c
    · intro i
      change toLocalizedPlane k e r s
          (ofLocalizedPlane k e r s
            (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X i))) =
        algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X i)
      simp only [ofLocalizedPlane, IsLocalization.Away.lift_eq]
      fin_cases i
      · change toLocalizedPlane k e r s (planeEval k e r s (X 0)) = _
        rw [planeEval_X_zero]
        exact toLocalizedPlane_x' k e r s
      · change toLocalizedPlane k e r s (planeEval k e r s (X 1)) = _
        rw [planeEval_X_one]
        exact toLocalizedPlane_y' k e r s

/-- The two special-case maps are inverse on `A[1/z]`. -/
theorem ofLocalizedPlane_comp_toLocalizedPlane (k : Type u) [CommRing k]
    (e r s : ℕ) :
    (ofLocalizedPlane k e r s).comp (toLocalizedPlane k e r s) =
      RingHom.id (Localization.Away (z k r s (1 + e * r * s))) :=
  by
    have hz : ofLocalizedPlane k e r s (zImage k r s) =
        algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s)))
          (z k r s (1 + e * r * s)) := by
      rw [zImage, ofLocalizedPlane, IsLocalization.Away.lift_eq, map_neg,
        planeRelation, map_add, map_pow, map_pow, planeEval_X_zero, planeEval_X_one,
        x'_pow_add_y'_pow, neg_neg]
    have hinv : IsLocalization.Away.invSelf (z k r s (1 + e * r * s)) *
        algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s)))
          (z k r s (1 + e * r * s)) = 1 := by
      exact (mul_comm _ _).trans (IsLocalization.Away.mul_invSelf _)
    apply IsLocalization.ringHom_ext (Submonoid.powers (z k r s (1 + e * r * s)))
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      change ofLocalizedPlane k e r s
          (toLocalizedPlane k e r s
            (algebraMap (Ring k r s (1 + e * r * s))
              (Localization.Away (z k r s (1 + e * r * s)))
              (Ideal.Quotient.mk _ (C c)))) =
        algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s))) (Ideal.Quotient.mk _ (C c))
      simp only [toLocalizedPlane, IsLocalization.Away.lift_eq, toLocalizedPlaneOnRing,
        Ideal.Quotient.lift_mk, spaceEval, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) (LocalizedPlane k r s)]
      change ofLocalizedPlane k e r s
          (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (C c)) = _
      simp only [ofLocalizedPlane, IsLocalization.Away.lift_eq, planeEval,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact IsScalarTower.algebraMap_apply k (Ring k r s (1 + e * r * s))
        (Localization.Away (z k r s (1 + e * r * s))) c
    · intro i
      change ofLocalizedPlane k e r s
          (toLocalizedPlane k e r s
            (algebraMap (Ring k r s (1 + e * r * s))
              (Localization.Away (z k r s (1 + e * r * s)))
              (Ideal.Quotient.mk _ (X i)))) =
        algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s))) (Ideal.Quotient.mk _ (X i))
      simp only [toLocalizedPlane, IsLocalization.Away.lift_eq, toLocalizedPlaneOnRing,
        Ideal.Quotient.lift_mk, spaceEval, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      fin_cases i
      · change ofLocalizedPlane k e r s
            (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 0) *
              zImage k r s ^ (e * s)) =
          algebraMap (Ring k r s (1 + e * r * s))
            (Localization.Away (z k r s (1 + e * r * s))) (x k r s (1 + e * r * s))
        rw [map_mul, map_pow, hz]
        simp only [ofLocalizedPlane, IsLocalization.Away.lift_eq, planeEval_X_zero]
        rw [x', mul_assoc (algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s))) (x k r s (1 + e * r * s))),
          ← mul_pow, hinv, one_pow, mul_one]
      · change ofLocalizedPlane k e r s
            (algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 1) *
              zImage k r s ^ (e * r)) =
          algebraMap (Ring k r s (1 + e * r * s))
            (Localization.Away (z k r s (1 + e * r * s))) (y k r s (1 + e * r * s))
        rw [map_mul, map_pow, hz]
        simp only [ofLocalizedPlane, IsLocalization.Away.lift_eq, planeEval_X_one]
        rw [y', mul_assoc (algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s))) (y k r s (1 + e * r * s))),
          ← mul_pow, hinv, one_pow, mul_one]
      · exact hz

/-- The isomorphism `A[1/z] ≃+* k[x', y', 1/z]` for `t = 1 + e * r * s`,
with `x' = x * z⁻¹ ^ (e * s)` and `y' = y * z⁻¹ ^ (e * r)`. -/
def awayEquiv (k : Type u) [CommRing k] (e r s : ℕ) :
    Localization.Away (z k r s (1 + e * r * s)) ≃+* LocalizedPlane k r s :=
  RingEquiv.ofRingHom (toLocalizedPlane k e r s) (ofLocalizedPlane k e r s)
    (toLocalizedPlane_comp_ofLocalizedPlane k e r s)
    (ofLocalizedPlane_comp_toLocalizedPlane k e r s)

/-- The forward map of `awayEquiv` is `toLocalizedPlane`. -/
theorem awayEquiv_toRingHom (k : Type u) [CommRing k] (e r s : ℕ) :
    (awayEquiv k e r s).toRingHom = toLocalizedPlane k e r s :=
  rfl

/-- The inverse map of `awayEquiv` is `ofLocalizedPlane`. -/
theorem awayEquiv_symm_toRingHom (k : Type u) [CommRing k] (e r s : ℕ) :
    (awayEquiv k e r s).symm.toRingHom = ofLocalizedPlane k e r s :=
  rfl

/-- The isomorphism sends `x'` to the first plane coordinate. -/
theorem awayEquiv_x' (k : Type u) [CommRing k] (e r s : ℕ) :
    awayEquiv k e r s (x' k e r s) =
      algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 0) :=
  toLocalizedPlane_x' k e r s

/-- The isomorphism sends `y'` to the second plane coordinate. -/
theorem awayEquiv_y' (k : Type u) [CommRing k] (e r s : ℕ) :
    awayEquiv k e r s (y' k e r s) =
      algebraMap (MvPolynomial (Fin 2) k) (LocalizedPlane k r s) (X 1) :=
  toLocalizedPlane_y' k e r s

/-- The isomorphism sends `z` to `-(x') ^ r - (y') ^ s`. -/
theorem awayEquiv_map_z (k : Type u) [CommRing k] (e r s : ℕ) :
    awayEquiv k e r s
        (algebraMap (Ring k r s (1 + e * r * s))
          (Localization.Away (z k r s (1 + e * r * s)))
          (z k r s (1 + e * r * s))) =
      zImage k r s :=
  by
    change toLocalizedPlane k e r s _ = _
    simp only [toLocalizedPlane, IsLocalization.Away.lift_eq]
    simp [toLocalizedPlaneOnRing, z, spaceEval, spaceSubst]

/-- A Pham–Brieskorn hypersurface over a field is factorial for pairwise
coprime exponents. -/
instance instUniqueFactorizationMonoid (k : Type u) [Field k] (r s t : ℕ)
    [Fact (Nat.Coprime r s)] [Fact (Nat.Coprime r t)] [Fact (Nat.Coprime s t)] :
    UniqueFactorizationMonoid (Ring k r s t) :=
  sorry

end MvPolynomial.PhamBrieskorn
