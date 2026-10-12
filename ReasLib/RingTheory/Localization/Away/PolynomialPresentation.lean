/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic

namespace Localization.Away.PolynomialPresentation

open Polynomial

universe u

noncomputable section

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
            (IsLocalization.Away.invSelf (C (π ^ ℓ) * X + 1))) = 1 := sorry

/-- The image of `π ^ ℓ t + 1` has the displayed inverse after sending `t` to `Φ(s)`. -/
theorem baseUnit_mul_inv
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let G : Type u := Localization.Away (C π * X + 1)
    let s : G := algebraMap (Polynomial A) G X
    let φs : G := aeval s Φ
    aeval φs (C (π ^ ℓ) * X + 1) *
        (IsLocalization.Away.invSelf (C π * X + 1) : G) ^ ℓ = 1 := sorry

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
    p.eval₂ (baseMap π ℓ Φ hΦ_shape) s = 0 := sorry

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

/-- The forward and backward maps compose to the identity on the quotient. -/
theorem forward_comp_backward
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let G : Type u := Localization.Away (C π * X + 1)
    (forward π ℓ hℓ_pos Φ hΦ_shape).comp (backward π ℓ Φ hΦ_shape) =
      AlgHom.id A (AdjoinRoot p) := sorry

/-- The backward and forward maps compose to the identity on the localization. -/
theorem backward_comp_forward
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    let G : Type u := Localization.Away (C π * X + 1)
    (backward π ℓ Φ hΦ_shape).comp (forward π ℓ hℓ_pos Φ hΦ_shape) =
      AlgHom.id A G := sorry

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
      AdjoinRoot.root p := sorry

/-- The equivalence agrees with the specified coefficient map from the localized base. -/
public theorem equiv_baseMap
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_shape : (C π * X + 1) ^ ℓ - 1 = C (π ^ ℓ) * Φ)
    (b : Localization.Away (C (π ^ ℓ) * X + 1)) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    let p : Polynomial B := Polynomial.map (algebraMap A B) Φ - C t
    equiv π ℓ hℓ_pos Φ hΦ_shape (baseMap π ℓ Φ hΦ_shape b) =
      algebraMap B (AdjoinRoot p) b := sorry

/-- Subtracting the localized variable preserves monicity in positive degree. -/
public theorem monic
    {A : Type u} [CommRing A] (π : A) (ℓ : ℕ) (hℓ_pos : 0 < ℓ) (Φ : Polynomial A)
    (hΦ_monic : Φ.Monic) (hΦ_degree : Φ.natDegree = ℓ) :
    let B : Type u := Localization.Away (C (π ^ ℓ) * X + 1)
    let t : B := algebraMap (Polynomial A) B X
    (Polynomial.map (algebraMap A B) Φ - C t).Monic := sorry

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
    (powerBasis π ℓ hℓ_pos Φ hΦ_monic hΦ_degree).gen = AdjoinRoot.root p := sorry

end
end Localization.Away.PolynomialPresentation
