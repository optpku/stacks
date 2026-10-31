/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic

namespace Localization.Away.PolynomialPresentation

open Polynomial

universe u

noncomputable section

private theorem aeval_root_sub_C
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (Φ : Polynomial A) (t : B) :
    let p := Polynomial.map (algebraMap A B) Φ - C t
    Polynomial.aeval (AdjoinRoot.root p) Φ = algebraMap B (AdjoinRoot p) t := by
  let p := Polynomial.map (algebraMap A B) Φ - C t
  have hp : Polynomial.aeval (AdjoinRoot.root p) p = 0 := by
    simpa only [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq] using
      AdjoinRoot.eval₂_root p
  exact sub_eq_zero.mp (by
    simpa only [p, Polynomial.aeval_sub, Polynomial.aeval_C,
      Polynomial.aeval_map_algebraMap] using hp)

/-- The image of `π s + 1` has the displayed inverse in the polynomial quotient. -/
theorem targetUnit_mul_inv
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let x : AdjoinRoot p := AdjoinRoot.root p
    aeval x (C π * X + 1) *
        ((aeval x (C π * X + 1)) ^ (ℓ - 1) *
          algebraMap B (AdjoinRoot p)
            (IsLocalization.Away.invSelf (C (π ^ ℓ) * X + 1))) = 1 := by
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
  let Q : Type u := AdjoinRoot p
  let x : Q := AdjoinRoot.root p
  let q : Polynomial A := C π * X + 1
  let d : Polynomial A := C (π ^ ℓ) * X + 1
  change Polynomial.aeval x q *
    ((Polynomial.aeval x q) ^ (ℓ - 1) * algebraMap B Q (IsLocalization.Away.invSelf d)) = 1
  have hroot : Polynomial.aeval x Φ = algebraMap B Q t := aeval_root_sub_C Φ t
  have hshape : (Polynomial.aeval x q) ^ ℓ - 1 =
      algebraMap A Q (π ^ ℓ) * Polynomial.aeval x Φ := by
    simpa only [map_sub, map_pow, map_one, map_mul, Polynomial.aeval_C] using
      congrArg (Polynomial.aeval x) hΦ_shape
  have hpow : (Polynomial.aeval x q) ^ ℓ =
      algebraMap B Q (algebraMap (Polynomial A) B d) := by
    calc
      (Polynomial.aeval x q) ^ ℓ = algebraMap A Q (π ^ ℓ) * Polynomial.aeval x Φ + 1 :=
        sub_eq_iff_eq_add.mp hshape
      _ = algebraMap B Q (algebraMap (Polynomial A) B d) := by
        rw [hroot, IsScalarTower.algebraMap_apply A B Q,
          IsScalarTower.algebraMap_apply A (Polynomial A) B]
        simp only [d, t, Polynomial.algebraMap_eq, map_add, map_mul, map_one]
  calc
    Polynomial.aeval x q *
        ((Polynomial.aeval x q) ^ (ℓ - 1) * algebraMap B Q (IsLocalization.Away.invSelf d)) =
        (Polynomial.aeval x q) ^ ℓ * algebraMap B Q (IsLocalization.Away.invSelf d) := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hℓ_pos]
    _ = algebraMap B Q (algebraMap (Polynomial A) B d) *
        algebraMap B Q (IsLocalization.Away.invSelf d) := by rw [hpow]
    _ = 1 := by
      simpa only [map_mul, map_one] using congrArg (algebraMap B Q)
        (IsLocalization.Away.mul_invSelf (S := B) d)

/-- The image of `π ^ ℓ t + 1` has the displayed inverse after sending `t` to `Φ(s)`. -/
theorem baseUnit_mul_inv
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let G : Type u := Localization.Away (C π * X + 1)
    let s : G := algebraMap (Polynomial A) G X
    let φs : G := aeval s Φ
    aeval φs (C (π ^ ℓ) * X + 1) *
        (IsLocalization.Away.invSelf (C π * X + 1) : G) ^ ℓ = 1 := by
  dsimp
  let G : Type u := Localization.Away (C π * X + 1)
  let s : G := algebraMap (Polynomial A) G X
  have hshape' := congrArg (Polynomial.aeval s) hΦ_shape
  have hshape'' : (Polynomial.aeval s (C π * X + 1)) ^ ℓ - 1 =
      algebraMap A G (π ^ ℓ) * Polynomial.aeval s Φ := by
    simpa using hshape'
  have hpow : (Polynomial.aeval s (C π * X + 1)) ^ ℓ =
      Polynomial.aeval (Polynomial.aeval s Φ) (C (π ^ ℓ) * X + 1) := by
    calc
      (Polynomial.aeval s (C π * X + 1)) ^ ℓ =
          algebraMap A G (π ^ ℓ) * Polynomial.aeval s Φ + 1 := by
            rw [← hshape'']
            ring
      _ = Polynomial.aeval (Polynomial.aeval s Φ) (C (π ^ ℓ) * X + 1) := by
            simp [mul_comm]
  have hq : Polynomial.aeval s (C π * X + 1) *
      (IsLocalization.Away.invSelf (C π * X + 1) : G) = 1 := by
    have hs : Polynomial.aeval s (C π * X + 1) =
        algebraMap (Polynomial A) G (C π * X + 1) := by
      simpa only [Algebra.algHom_apply, Polynomial.aeval_X_left_apply, s] using
        (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom A (Polynomial A) G)
          X (C π * X + 1))
    rw [hs]
    exact IsLocalization.Away.mul_invSelf _
  calc
    Polynomial.aeval (Polynomial.aeval s Φ) (C (π ^ ℓ) * X + 1) *
          (IsLocalization.Away.invSelf (C π * X + 1) : G) ^ ℓ =
        (Polynomial.aeval s (C π * X + 1)) ^ ℓ *
          (IsLocalization.Away.invSelf (C π * X + 1) : G) ^ ℓ := by
      rw [hpow]
    _ = (Polynomial.aeval s (C π * X + 1) *
          (IsLocalization.Away.invSelf (C π * X + 1) : G)) ^ ℓ := by
      rw [mul_pow]
    _ = 1 := by rw [hq, one_pow]

/-- The denominator `π s + 1` is represented by an explicit unit. -/
noncomputable def targetUnit
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let x : AdjoinRoot p := AdjoinRoot.root p
    (AdjoinRoot p)ˣ :=
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
  let x : AdjoinRoot p := AdjoinRoot.root p
  Units.mkOfMulEqOne
    (aeval x (C π * X + 1))
    ((aeval x (C π * X + 1)) ^ (ℓ - 1) *
      algebraMap B (AdjoinRoot p)
        (IsLocalization.Away.invSelf (C (π ^ ℓ) * X + 1)))
    (targetUnit_mul_inv π ℓ hℓ_pos Φ hΦ_shape)

/-- The substituted denominator `π ^ ℓ t + 1` is represented by an explicit unit. -/
noncomputable def baseUnit
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let G : Type u := Localization.Away (C π * X + 1)
    let s : G := algebraMap (Polynomial A) G X
    let φs : G := aeval s Φ
    Gˣ :=
  let G : Type u := Localization.Away (C π * X + 1)
  let s : G := algebraMap (Polynomial A) G X
  let φs : G := aeval s Φ
  Units.mkOfMulEqOne
    (aeval φs (C (π ^ ℓ) * X + 1))
    ((IsLocalization.Away.invSelf (C π * X + 1) : G) ^ ℓ)
    (baseUnit_mul_inv π ℓ Φ hΦ_shape)

/-- The forward algebra map sends the localized variable to the adjoined root. -/
noncomputable def forward
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    Localization.Away (C π * X + 1) →ₐ[A] AdjoinRoot p :=
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
  IsLocalization.Away.liftAlgHom (C π * X + 1)
    (targetUnit π ℓ hℓ_pos Φ hΦ_shape).isUnit

/-- The coefficient algebra map sends the localized variable to `Φ(s)`. -/
public noncomputable def baseMap
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let G : Type u := Localization.Away (C π * X + 1)
    B →ₐ[A] G :=
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let G : Type u := Localization.Away (C π * X + 1)
  IsLocalization.Away.liftAlgHom (C (π ^ ℓ) * X + 1)
    (baseUnit π ℓ Φ hΦ_shape).isUnit

/-- The defining polynomial relation vanishes under the coefficient map and `s`. -/
theorem rootRelation
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let G : Type u := Localization.Away (C π * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let s : G := algebraMap (Polynomial A) G X
    p.eval₂ (baseMap π ℓ Φ hΦ_shape) s = 0 := by
  dsimp
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_map, Polynomial.eval₂_C]
  simp [baseMap, IsLocalization.Away.liftAlgHom_apply, Polynomial.aeval_def]

/-- The backward algebra map evaluates the quotient root at the localized variable. -/
noncomputable def backward
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let G : Type u := Localization.Away (C π * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let s : G := algebraMap (Polynomial A) G X
    AdjoinRoot p →ₐ[A] G :=
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let G : Type u := Localization.Away (C π * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
  let s : G := algebraMap (Polynomial A) G X
  AdjoinRoot.liftAlgHom p (baseMap π ℓ Φ hΦ_shape) s
    (rootRelation π ℓ Φ hΦ_shape)

private theorem forward_baseMap
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    (forward π ℓ hℓ_pos Φ hΦ_shape).comp (baseMap π ℓ Φ hΦ_shape) =
      Algebra.algHom A B (AdjoinRoot p) := by
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
  let G : Type u := Localization.Away (C π * X + 1)
  let s : G := algebraMap (Polynomial A) G X
  apply Localization.algHom_ext (Submonoid.powers (C (π ^ ℓ) * X + 1))
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply]
  simp only [baseMap, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
  change (forward π ℓ hℓ_pos Φ hΦ_shape) (Polynomial.aeval s Φ) =
    algebraMap B (AdjoinRoot p) t
  rw [← Polynomial.aeval_algHom_apply]
  have hs : (forward π ℓ hℓ_pos Φ hΦ_shape) s = AdjoinRoot.root p := by
    dsimp only [s, G, p, t, B]
    simp [forward]
  rw [hs]
  exact aeval_root_sub_C Φ t

/-- The forward and backward maps compose to the identity on the quotient. -/
theorem forward_comp_backward
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let G : Type u := Localization.Away (C π * X + 1)
    (forward π ℓ hℓ_pos Φ hΦ_shape).comp (backward π ℓ Φ hΦ_shape) =
      AlgHom.id A (AdjoinRoot p) := by
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
  change (forward π ℓ hℓ_pos Φ hΦ_shape).comp (backward π ℓ Φ hΦ_shape) =
    AlgHom.id A (AdjoinRoot p)
  apply AdjoinRoot.algHom_ext'
  · apply AlgHom.ext
    intro b
    simpa [backward, Algebra.algHom, p, t, B, AlgHom.id] using
      AlgHom.congr_fun (forward_baseMap π ℓ hℓ_pos Φ hΦ_shape) b
  · simp [backward, forward, p, t, B, AlgHom.id]

/-- The backward and forward maps compose to the identity on the localization. -/
theorem backward_comp_forward
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let G : Type u := Localization.Away (C π * X + 1)
    (backward π ℓ Φ hΦ_shape).comp (forward π ℓ hℓ_pos Φ hΦ_shape) =
      AlgHom.id A G := by
  dsimp
  apply Localization.algHom_ext (Submonoid.powers (C π * X + 1))
  apply Polynomial.algHom_ext
  simp [AlgHom.comp_apply, Algebra.algHom, forward, backward,
    IsLocalization.Away.liftAlgHom_apply]

/-- The polynomial localization is equivalent to the corresponding adjoined-root quotient. -/
public noncomputable def equiv
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    Localization.Away (C π * X + 1) ≃ₐ[A]
      AdjoinRoot (Polynomial.map (algebraMap A B) Φ - C t) :=
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
  AlgEquiv.ofAlgHom
    (forward π ℓ hℓ_pos Φ hΦ_shape)
    (backward π ℓ Φ hΦ_shape)
    (forward_comp_backward π ℓ hℓ_pos Φ hΦ_shape)
    (backward_comp_forward π ℓ hℓ_pos Φ hΦ_shape)

/-- The equivalence sends the polynomial variable to the adjoined root. -/
public theorem equiv_apply
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    equiv π ℓ hℓ_pos Φ hΦ_shape
        (algebraMap (Polynomial A) (Localization.Away (C π * X + 1)) X) =
      AdjoinRoot.root p := by
  dsimp
  simp [equiv, forward]

/-- The equivalence agrees with the specified coefficient map from the localized base. -/
public theorem equiv_baseMap
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ)
    (b : Localization.Away (C (π ^ ℓ) * X + 1)) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    equiv π ℓ hℓ_pos Φ hΦ_shape (baseMap π ℓ Φ hΦ_shape b) =
      algebraMap B (AdjoinRoot p) b := by
  simpa [equiv, Algebra.algHom] using
    AlgHom.congr_fun (forward_baseMap π ℓ hℓ_pos Φ hΦ_shape) b

/-- Subtracting the localized variable preserves monicity in positive degree. -/
public theorem monic
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_monic : Φ.Monic) (hΦ_degree : Φ.natDegree = ℓ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    (Polynomial.map (algebraMap A B) Φ - C t).Monic := by
  dsimp
  rcases subsingleton_or_nontrivial (Localization.Away (C (π ^ ℓ) * X + 1)) with hB | hB
  · letI := hB
    exact Polynomial.monic_of_subsingleton _
  · letI := hB
    apply Polynomial.Monic.sub_of_left
    · exact hΦ_monic.map (algebraMap A _)
    · apply Polynomial.degree_lt_degree
      rw [Polynomial.natDegree_C, hΦ_monic.natDegree_map, hΦ_degree]
      exact hℓ_pos

/-- The adjoined-root quotient has the canonical power basis over the localized base. -/
public noncomputable def powerBasis
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_monic : Φ.Monic) (hΦ_degree : Φ.natDegree = ℓ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    PowerBasis B (AdjoinRoot (Polynomial.map (algebraMap A B) Φ - C t)) :=
  let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
  let t : B := algebraMap (Polynomial A) B X
  AdjoinRoot.powerBasis' (monic π ℓ hℓ_pos Φ hΦ_monic hΦ_degree)

/-- The generator of the canonical power basis is the quotient root. -/
public theorem powerBasis_gen
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_monic : Φ.Monic) (hΦ_degree : Φ.natDegree = ℓ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    (powerBasis π ℓ hℓ_pos Φ hΦ_monic hΦ_degree).gen = AdjoinRoot.root p := by
  rfl

end
end Localization.Away.PolynomialPresentation
