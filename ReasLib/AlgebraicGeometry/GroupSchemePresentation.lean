/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.RingTheory.Localization.Away.PolynomialPresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

@[expose] public section

open Polynomial TensorProduct CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- The cyclotomic integer ring `A = ℤ[ζ]` for a prime `ℓ`. -/
public abbrev cyclotomicIntegers (ℓ : ℕ) : Type :=
  AdjoinRoot (cyclotomic ℓ ℤ)

/-- The uniformizer `π = ζ - 1` in the cyclotomic integers. -/
public noncomputable def presentationPi (ℓ : ℕ) : cyclotomicIntegers ℓ :=
  AdjoinRoot.root (cyclotomic ℓ ℤ) - 1

/-- The monic degree-`ℓ` polynomial `Φ` uniquely determined by
`(π s + 1) ^ ℓ - 1 = π ^ ℓ Φ(s)`. It is the monic polynomial with roots
`σ_i = ∑_{k < i} ζ ^ k = (ζ ^ i - 1) / π`. -/
public noncomputable def presentationPhi (ℓ : ℕ) :
    Polynomial (cyclotomicIntegers ℓ) :=
  ∏ i ∈ Finset.range ℓ,
    (X - C (∑ k ∈ Finset.range i, AdjoinRoot.root (cyclotomic ℓ ℤ) ^ k))

/-- `Φ` realises the identity `(π s + 1) ^ ℓ - 1 = π ^ ℓ Φ(s)`. -/
public theorem presentationPhi_shape (ℓ : ℕ) :
    (C (presentationPi ℓ) * X + 1) ^ ℓ - 1 =
      C (presentationPi ℓ ^ ℓ) * presentationPhi ℓ := sorry

/-- `Φ` is monic. -/
public theorem presentationPhi_monic (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    (presentationPhi ℓ).Monic := sorry

/-- `Φ` has degree `ℓ`. -/
public theorem presentationPhi_natDegree (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    (presentationPhi ℓ).natDegree = ℓ := sorry

/-- Coordinate ring of `G`: `A[s, 1 / (π s + 1)]`. -/
public noncomputable abbrev presentationGCoord (ℓ : ℕ) : Type :=
  Localization.Away (C (presentationPi ℓ) * X + 1)

/-- Coordinate ring of `H`: `A[t, 1 / (π ^ ℓ t + 1)]`. -/
public noncomputable abbrev presentationHCoord (ℓ : ℕ) : Type :=
  Localization.Away (C (presentationPi ℓ ^ ℓ) * X + 1)

/-- The distinguished coordinate `s` on `G`. -/
public noncomputable def presentationG_s (ℓ : ℕ) : presentationGCoord ℓ :=
  algebraMap (Polynomial (cyclotomicIntegers ℓ)) (presentationGCoord ℓ) X

/-- The distinguished coordinate `t` on `H`. -/
public noncomputable def presentationH_t (ℓ : ℕ) : presentationHCoord ℓ :=
  algebraMap (Polynomial (cyclotomicIntegers ℓ)) (presentationHCoord ℓ) X

/-- `G` as an affine scheme over `Spec A`. -/
public noncomputable def presentationGOver (ℓ : ℕ) :
    Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))) :=
  Over.mk
    (Spec.map
      (CommRingCat.ofHom
        (algebraMap (cyclotomicIntegers ℓ) (presentationGCoord ℓ))))

/-- `H` as an affine scheme over `Spec A`. -/
public noncomputable def presentationHOver (ℓ : ℕ) :
    Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))) :=
  Over.mk
    (Spec.map
      (CommRingCat.ofHom
        (algebraMap (cyclotomicIntegers ℓ) (presentationHCoord ℓ))))

/-- The identity section of `G` is the counit sending `s` to `0`. -/
public theorem presentationGCounit_isUnit (ℓ : ℕ) :
    IsUnit
      (aeval (0 : cyclotomicIntegers ℓ)
        (C (presentationPi ℓ) * X + 1)) := sorry

/-- Counit of the Hopf algebra of `G`. -/
public noncomputable def presentationGCounit (ℓ : ℕ) :
    presentationGCoord ℓ →ₐ[cyclotomicIntegers ℓ] cyclotomicIntegers ℓ :=
  IsLocalization.Away.liftAlgHom (C (presentationPi ℓ) * X + 1)
    (presentationGCounit_isUnit ℓ)

/-- The identity section of `H` is the counit sending `t` to `0`. -/
public theorem presentationHCounit_isUnit (ℓ : ℕ) :
    IsUnit
      (aeval (0 : cyclotomicIntegers ℓ)
        (C (presentationPi ℓ ^ ℓ) * X + 1)) := sorry

/-- Counit of the Hopf algebra of `H`. -/
public noncomputable def presentationHCounit (ℓ : ℕ) :
    presentationHCoord ℓ →ₐ[cyclotomicIntegers ℓ] cyclotomicIntegers ℓ :=
  IsLocalization.Away.liftAlgHom (C (presentationPi ℓ ^ ℓ) * X + 1)
    (presentationHCounit_isUnit ℓ)

/-- Unit morphism of `G` on underlying schemes. -/
public noncomputable def presentationGOneLeft (ℓ : ℕ) :
    (𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))))).left ⟶
      (presentationGOver ℓ).left :=
  Spec.map (CommRingCat.ofHom (presentationGCounit ℓ).toRingHom)

/-- The unit of `G` lies over `Spec A`. -/
public theorem presentationGOneLeft_w (ℓ : ℕ) :
    presentationGOneLeft ℓ ≫ (presentationGOver ℓ).hom =
      (𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))))).hom :=
  sorry

/-- Unit morphism of `G` in `Over (Spec A)`. -/
public noncomputable def presentationGOne (ℓ : ℕ) :
    𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ)))) ⟶
      presentationGOver ℓ :=
  Over.homMk (presentationGOneLeft ℓ) (presentationGOneLeft_w ℓ)

/-- Unit morphism of `H` on underlying schemes. -/
public noncomputable def presentationHOneLeft (ℓ : ℕ) :
    (𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))))).left ⟶
      (presentationHOver ℓ).left :=
  Spec.map (CommRingCat.ofHom (presentationHCounit ℓ).toRingHom)

/-- The unit of `H` lies over `Spec A`. -/
public theorem presentationHOneLeft_w (ℓ : ℕ) :
    presentationHOneLeft ℓ ≫ (presentationHOver ℓ).hom =
      (𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))))).hom :=
  sorry

/-- Unit morphism of `H` in `Over (Spec A)`. -/
public noncomputable def presentationHOne (ℓ : ℕ) :
    𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ)))) ⟶
      presentationHOver ℓ :=
  Over.homMk (presentationHOneLeft ℓ) (presentationHOneLeft_w ℓ)

/-- Left and right copies of the coordinate `s` in `G ⊗_A G`. -/
public noncomputable def presentationG_sLeft (ℓ : ℕ) :
    presentationGCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationGCoord ℓ :=
  Algebra.TensorProduct.includeLeft (S := cyclotomicIntegers ℓ)
    (presentationG_s ℓ)

/-- Right copy of the coordinate `s` in `G ⊗_A G`. -/
public noncomputable def presentationG_sRight (ℓ : ℕ) :
    presentationGCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationGCoord ℓ :=
  Algebra.TensorProduct.includeRight (R := cyclotomicIntegers ℓ)
    (presentationG_s ℓ)

/-- Image of the denominator `π s + 1` under comultiplication. -/
public noncomputable def presentationGComulDenom (ℓ : ℕ) :
    presentationGCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationGCoord ℓ :=
  1 + presentationPi ℓ •
    (presentationG_sLeft ℓ + presentationG_sRight ℓ +
      presentationPi ℓ • (presentationG_sLeft ℓ * presentationG_sRight ℓ))

/-- Inverse of the comultiplied denominator. -/
public noncomputable def presentationGComulDenomInv (ℓ : ℕ) :
    presentationGCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationGCoord ℓ :=
  Algebra.TensorProduct.includeLeft (S := cyclotomicIntegers ℓ)
      (IsLocalization.Away.invSelf (C (presentationPi ℓ) * X + 1)) *
    Algebra.TensorProduct.includeRight (R := cyclotomicIntegers ℓ)
      (IsLocalization.Away.invSelf (C (presentationPi ℓ) * X + 1))

/-- The comultiplied denominator is a unit. -/
public theorem presentationGComulDenom_val_inv (ℓ : ℕ) :
    presentationGComulDenom ℓ * presentationGComulDenomInv ℓ = 1 := sorry

/-- Reverse product for the comultiplied denominator unit. -/
public theorem presentationGComulDenom_inv_val (ℓ : ℕ) :
    presentationGComulDenomInv ℓ * presentationGComulDenom ℓ = 1 := sorry

/-- Unit structure on the comultiplied denominator of `G`. -/
public noncomputable def presentationGComulDenomUnit (ℓ : ℕ) :
    (presentationGCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationGCoord ℓ)ˣ where
  val := presentationGComulDenom ℓ
  inv := presentationGComulDenomInv ℓ
  val_inv := presentationGComulDenom_val_inv ℓ
  inv_val := presentationGComulDenom_inv_val ℓ

/-- The polynomial comultiplication of `G` sends `s` to
`s ⊗ 1 + 1 ⊗ s + π (s ⊗ s)`. -/
public noncomputable def presentationGComulPoly (ℓ : ℕ) :
    Polynomial (cyclotomicIntegers ℓ) →ₐ[cyclotomicIntegers ℓ]
      presentationGCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationGCoord ℓ :=
  aeval
    (presentationG_sLeft ℓ + presentationG_sRight ℓ +
      presentationPi ℓ • (presentationG_sLeft ℓ * presentationG_sRight ℓ))

/-- The image of `π s + 1` under `presentationGComulPoly` is a unit. -/
public theorem presentationGComulPoly_isUnit (ℓ : ℕ) :
    IsUnit (presentationGComulPoly ℓ (C (presentationPi ℓ) * X + 1)) := sorry

/-- Comultiplication on the coordinate ring of `G`. -/
public noncomputable def presentationGComul (ℓ : ℕ) :
    presentationGCoord ℓ →ₐ[cyclotomicIntegers ℓ]
      presentationGCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationGCoord ℓ :=
  IsLocalization.Away.liftAlgHom (C (presentationPi ℓ) * X + 1)
    (presentationGComulPoly_isUnit ℓ)

/-- Left and right copies of the coordinate `t` in `H ⊗_A H`. -/
public noncomputable def presentationH_tLeft (ℓ : ℕ) :
    presentationHCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationHCoord ℓ :=
  Algebra.TensorProduct.includeLeft (S := cyclotomicIntegers ℓ)
    (presentationH_t ℓ)

/-- Right copy of the coordinate `t` in `H ⊗_A H`. -/
public noncomputable def presentationH_tRight (ℓ : ℕ) :
    presentationHCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationHCoord ℓ :=
  Algebra.TensorProduct.includeRight (R := cyclotomicIntegers ℓ)
    (presentationH_t ℓ)

/-- Image of the denominator `π ^ ℓ t + 1` under comultiplication. -/
public noncomputable def presentationHComulDenom (ℓ : ℕ) :
    presentationHCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationHCoord ℓ :=
  1 + (presentationPi ℓ ^ ℓ) •
    (presentationH_tLeft ℓ + presentationH_tRight ℓ +
      (presentationPi ℓ ^ ℓ) • (presentationH_tLeft ℓ * presentationH_tRight ℓ))

/-- Inverse of the comultiplied denominator of `H`. -/
public noncomputable def presentationHComulDenomInv (ℓ : ℕ) :
    presentationHCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationHCoord ℓ :=
  Algebra.TensorProduct.includeLeft (S := cyclotomicIntegers ℓ)
      (IsLocalization.Away.invSelf (C (presentationPi ℓ ^ ℓ) * X + 1)) *
    Algebra.TensorProduct.includeRight (R := cyclotomicIntegers ℓ)
      (IsLocalization.Away.invSelf (C (presentationPi ℓ ^ ℓ) * X + 1))

/-- The comultiplied denominator of `H` is a unit. -/
public theorem presentationHComulDenom_val_inv (ℓ : ℕ) :
    presentationHComulDenom ℓ * presentationHComulDenomInv ℓ = 1 := sorry

/-- Reverse product for the comultiplied denominator unit of `H`. -/
public theorem presentationHComulDenom_inv_val (ℓ : ℕ) :
    presentationHComulDenomInv ℓ * presentationHComulDenom ℓ = 1 := sorry

/-- Unit structure on the comultiplied denominator of `H`. -/
public noncomputable def presentationHComulDenomUnit (ℓ : ℕ) :
    (presentationHCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationHCoord ℓ)ˣ where
  val := presentationHComulDenom ℓ
  inv := presentationHComulDenomInv ℓ
  val_inv := presentationHComulDenom_val_inv ℓ
  inv_val := presentationHComulDenom_inv_val ℓ

/-- The polynomial comultiplication of `H`. -/
public noncomputable def presentationHComulPoly (ℓ : ℕ) :
    Polynomial (cyclotomicIntegers ℓ) →ₐ[cyclotomicIntegers ℓ]
      presentationHCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationHCoord ℓ :=
  aeval
    (presentationH_tLeft ℓ + presentationH_tRight ℓ +
      (presentationPi ℓ ^ ℓ) • (presentationH_tLeft ℓ * presentationH_tRight ℓ))

/-- The image of `π ^ ℓ t + 1` under `presentationHComulPoly` is a unit. -/
public theorem presentationHComulPoly_isUnit (ℓ : ℕ) :
    IsUnit (presentationHComulPoly ℓ (C (presentationPi ℓ ^ ℓ) * X + 1)) := sorry

/-- Comultiplication on the coordinate ring of `H`. -/
public noncomputable def presentationHComul (ℓ : ℕ) :
    presentationHCoord ℓ →ₐ[cyclotomicIntegers ℓ]
      presentationHCoord ℓ ⊗[cyclotomicIntegers ℓ] presentationHCoord ℓ :=
  IsLocalization.Away.liftAlgHom (C (presentationPi ℓ ^ ℓ) * X + 1)
    (presentationHComulPoly_isUnit ℓ)

/-- Underlying scheme map of multiplication on `G`. -/
public noncomputable def presentationGMulLeft (ℓ : ℕ) :
    (presentationGOver ℓ ⊗ presentationGOver ℓ).left ⟶
      (presentationGOver ℓ).left :=
  (pullbackSpecIso (cyclotomicIntegers ℓ)
      (presentationGCoord ℓ) (presentationGCoord ℓ)).hom ≫
    Spec.map (CommRingCat.ofHom (presentationGComul ℓ).toRingHom)

/-- Multiplication on `G` lies over `Spec A`. -/
public theorem presentationGMulLeft_w (ℓ : ℕ) :
    presentationGMulLeft ℓ ≫ (presentationGOver ℓ).hom =
      (presentationGOver ℓ ⊗ presentationGOver ℓ).hom := sorry

/-- Multiplication morphism of `G`. -/
public noncomputable def presentationGMul (ℓ : ℕ) :
    presentationGOver ℓ ⊗ presentationGOver ℓ ⟶ presentationGOver ℓ :=
  Over.homMk (presentationGMulLeft ℓ) (presentationGMulLeft_w ℓ)

/-- Underlying scheme map of multiplication on `H`. -/
public noncomputable def presentationHMulLeft (ℓ : ℕ) :
    (presentationHOver ℓ ⊗ presentationHOver ℓ).left ⟶
      (presentationHOver ℓ).left :=
  (pullbackSpecIso (cyclotomicIntegers ℓ)
      (presentationHCoord ℓ) (presentationHCoord ℓ)).hom ≫
    Spec.map (CommRingCat.ofHom (presentationHComul ℓ).toRingHom)

/-- Multiplication on `H` lies over `Spec A`. -/
public theorem presentationHMulLeft_w (ℓ : ℕ) :
    presentationHMulLeft ℓ ≫ (presentationHOver ℓ).hom =
      (presentationHOver ℓ ⊗ presentationHOver ℓ).hom := sorry

/-- Multiplication morphism of `H`. -/
public noncomputable def presentationHMul (ℓ : ℕ) :
    presentationHOver ℓ ⊗ presentationHOver ℓ ⟶ presentationHOver ℓ :=
  Over.homMk (presentationHMulLeft ℓ) (presentationHMulLeft_w ℓ)

/-- The inversion denominator `π s + 1` remains a unit after `s ↦ -s / (π s + 1)`. -/
public theorem presentationGInv_isUnit (ℓ : ℕ) :
    IsUnit
      (aeval
        (-presentationG_s ℓ *
          IsLocalization.Away.invSelf (C (presentationPi ℓ) * X + 1))
        (C (presentationPi ℓ) * X + 1)) := sorry

/-- Antipode of the coordinate ring of `G`. -/
public noncomputable def presentationGAntipode (ℓ : ℕ) :
    presentationGCoord ℓ →ₐ[cyclotomicIntegers ℓ] presentationGCoord ℓ :=
  IsLocalization.Away.liftAlgHom (C (presentationPi ℓ) * X + 1)
    (presentationGInv_isUnit ℓ)

/-- The inversion denominator of `H` remains a unit after the analogous antipode. -/
public theorem presentationHInv_isUnit (ℓ : ℕ) :
    IsUnit
      (aeval
        (-presentationH_t ℓ *
          IsLocalization.Away.invSelf (C (presentationPi ℓ ^ ℓ) * X + 1))
        (C (presentationPi ℓ ^ ℓ) * X + 1)) := sorry

/-- Antipode of the coordinate ring of `H`. -/
public noncomputable def presentationHAntipode (ℓ : ℕ) :
    presentationHCoord ℓ →ₐ[cyclotomicIntegers ℓ] presentationHCoord ℓ :=
  IsLocalization.Away.liftAlgHom (C (presentationPi ℓ ^ ℓ) * X + 1)
    (presentationHInv_isUnit ℓ)

/-- Underlying scheme map of inversion on `G`. -/
public noncomputable def presentationGInvLeft (ℓ : ℕ) :
    (presentationGOver ℓ).left ⟶ (presentationGOver ℓ).left :=
  Spec.map (CommRingCat.ofHom (presentationGAntipode ℓ).toRingHom)

/-- Inversion on `G` lies over `Spec A`. -/
public theorem presentationGInvLeft_w (ℓ : ℕ) :
    presentationGInvLeft ℓ ≫ (presentationGOver ℓ).hom =
      (presentationGOver ℓ).hom := sorry

/-- Inversion morphism of `G`. -/
public noncomputable def presentationGInv (ℓ : ℕ) :
    presentationGOver ℓ ⟶ presentationGOver ℓ :=
  Over.homMk (presentationGInvLeft ℓ) (presentationGInvLeft_w ℓ)

/-- Underlying scheme map of inversion on `H`. -/
public noncomputable def presentationHInvLeft (ℓ : ℕ) :
    (presentationHOver ℓ).left ⟶ (presentationHOver ℓ).left :=
  Spec.map (CommRingCat.ofHom (presentationHAntipode ℓ).toRingHom)

/-- Inversion on `H` lies over `Spec A`. -/
public theorem presentationHInvLeft_w (ℓ : ℕ) :
    presentationHInvLeft ℓ ≫ (presentationHOver ℓ).hom =
      (presentationHOver ℓ).hom := sorry

/-- Inversion morphism of `H`. -/
public noncomputable def presentationHInv (ℓ : ℕ) :
    presentationHOver ℓ ⟶ presentationHOver ℓ :=
  Over.homMk (presentationHInvLeft ℓ) (presentationHInvLeft_w ℓ)

/-- Group-object structure on the affine scheme `G`. -/
public noncomputable instance instGrpObjPresentationGOver (ℓ : ℕ) :
    GrpObj (presentationGOver ℓ) where
  one := presentationGOne ℓ
  mul := presentationGMul ℓ
  inv := presentationGInv ℓ
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- Group-object structure on the affine scheme `H`. -/
public noncomputable instance instGrpObjPresentationHOver (ℓ : ℕ) :
    GrpObj (presentationHOver ℓ) where
  one := presentationHOne ℓ
  mul := presentationHMul ℓ
  inv := presentationHInv ℓ
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The affine group scheme `G = Spec(A[s, 1 / (π s + 1)])` over `A`. -/
public noncomputable def presentationG (ℓ : ℕ) :
    GroupScheme (Spec (CommRingCat.of (cyclotomicIntegers ℓ))) where
  X := presentationGOver ℓ

/-- The affine group scheme `H = Spec(A[t, 1 / (π ^ ℓ t + 1)])` over `A`. -/
public noncomputable def presentationH (ℓ : ℕ) :
    GroupScheme (Spec (CommRingCat.of (cyclotomicIntegers ℓ))) where
  X := presentationHOver ℓ

/-- The underlying scheme of `presentationG` is the spectrum of its coordinate ring. -/
public theorem presentationG_X (ℓ : ℕ) :
    (presentationG ℓ).X.left =
      Spec (CommRingCat.of (presentationGCoord ℓ)) := sorry

/-- The underlying scheme of `presentationH` is the spectrum of its coordinate ring. -/
public theorem presentationH_X (ℓ : ℕ) :
    (presentationH ℓ).X.left =
      Spec (CommRingCat.of (presentationHCoord ℓ)) := sorry

/-- Underlying scheme map of `G → H` induced by `t ↦ Φ(s)`. -/
public noncomputable def presentationHomLeft (ℓ : ℕ) :
    (presentationG ℓ).X.left ⟶ (presentationH ℓ).X.left :=
  Spec.map
    (CommRingCat.ofHom
      (Localization.Away.PolynomialPresentation.baseMap (presentationPi ℓ) ℓ (presentationPhi ℓ)
        (presentationPhi_shape ℓ)).toRingHom)

/-- `presentationHomLeft` lies over `Spec A`. -/
public theorem presentationHomLeft_w (ℓ : ℕ) :
    presentationHomLeft ℓ ≫ (presentationH ℓ).X.hom =
      (presentationG ℓ).X.hom := sorry

/-- `G → H` as a morphism of schemes over `A`. -/
public noncomputable def presentationHomOver (ℓ : ℕ) :
    (presentationG ℓ).X ⟶ (presentationH ℓ).X :=
  Over.homMk (presentationHomLeft ℓ) (presentationHomLeft_w ℓ)

/-- The homomorphism `G → H` preserves units. -/
public theorem presentationHomOver_one (ℓ : ℕ) :
    η[(presentationG ℓ).X] ≫ presentationHomOver ℓ = η[(presentationH ℓ).X] := sorry

/-- The homomorphism `G → H` preserves multiplication. -/
public theorem presentationHomOver_mul (ℓ : ℕ) :
    μ[(presentationG ℓ).X] ≫ presentationHomOver ℓ =
      (presentationHomOver ℓ ⊗ₘ presentationHomOver ℓ) ≫ μ[(presentationH ℓ).X] :=
  sorry

/-- The homomorphism `G → H` is a morphism of monoid objects. -/
public noncomputable instance instIsMonHomPresentationHomOver (ℓ : ℕ) :
    IsMonHom (presentationHomOver ℓ) := sorry

/-- The homomorphism `f : G → H` of group schemes over `A`. -/
public noncomputable def presentationHom (ℓ : ℕ) :
    presentationG ℓ ⟶ presentationH ℓ where
  hom := { hom := presentationHomOver ℓ }

/-- On coordinate rings, `presentationHom` is `Localization.Away.PolynomialPresentation.baseMap`. -/
public theorem presentationHom_spec (ℓ : ℕ) :
    presentationHomLeft ℓ =
      Spec.map
        (CommRingCat.ofHom
          (Localization.Away.PolynomialPresentation.baseMap (presentationPi ℓ) ℓ (presentationPhi ℓ)
            (presentationPhi_shape ℓ)).toRingHom) := sorry

/-- Coordinate ring of the finite constant group scheme `underline(Z / ℓ Z)_A`,
as the product ring `A^(ZMod ℓ)`. -/
public abbrev constantZModCoord (ℓ : ℕ) : Type :=
  ZMod ℓ → cyclotomicIntegers ℓ

/-- The constant scheme `Spec (A^(ZMod ℓ))` over `Spec A`, equivalently the
coproduct `∐_{i : ZMod ℓ} Spec A`. -/
public noncomputable def constantZModOver (ℓ : ℕ) :
    Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))) :=
  Over.mk
    (Spec.map
      (CommRingCat.ofHom
        (algebraMap (cyclotomicIntegers ℓ) (constantZModCoord ℓ))))

/-- The `A`-coordinate of the section `σ_i`, equal to `(ζ ^ i - 1) / π`. -/
public noncomputable def sigmaCoord (ℓ : ℕ) (i : ZMod ℓ) :
    cyclotomicIntegers ℓ :=
  ∑ k ∈ Finset.range i.val, AdjoinRoot.root (cyclotomic ℓ ℤ) ^ k

/-- `π σ_i + 1` is a unit, equal to `ζ ^ i`. -/
public theorem sigmaCoord_denom_isUnit (ℓ : ℕ) (i : ZMod ℓ) :
    IsUnit (aeval (sigmaCoord ℓ i) (C (presentationPi ℓ) * X + 1)) := sorry

/-- The algebra map `A[s, 1 / (π s + 1)] → A` sending `s` to `σ_i`. -/
public noncomputable def sigmaPointAlgHom (ℓ : ℕ) (i : ZMod ℓ) :
    presentationGCoord ℓ →ₐ[cyclotomicIntegers ℓ] cyclotomicIntegers ℓ :=
  IsLocalization.Away.liftAlgHom (C (presentationPi ℓ) * X + 1)
    (sigmaCoord_denom_isUnit ℓ i)

/-- Underlying scheme map of the section `σ_i : Spec A → G`. -/
public noncomputable def sigmaPointLeft (ℓ : ℕ) (i : ZMod ℓ) :
    (𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))))).left ⟶
      (presentationG ℓ).X.left :=
  Spec.map (CommRingCat.ofHom (sigmaPointAlgHom ℓ i).toRingHom)

/-- The section `σ_i` lies over `Spec A`. -/
public theorem sigmaPointLeft_w (ℓ : ℕ) (i : ZMod ℓ) :
    sigmaPointLeft ℓ i ≫ (presentationG ℓ).X.hom =
      (𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))))).hom :=
  sorry

/-- The `A`-point `σ_i` of `G`. -/
public noncomputable def sigmaPoint (ℓ : ℕ) (i : ZMod ℓ) :
    𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ)))) ⟶
      (presentationG ℓ).X :=
  Over.homMk (sigmaPointLeft ℓ i) (sigmaPointLeft_w ℓ i)

/-- The sections `σ_i` are a group homomorphism in `i`. -/
public theorem sigmaPoint_add (ℓ : ℕ) (i j : ZMod ℓ) :
    CartesianMonoidalCategory.lift (sigmaPoint ℓ i) (sigmaPoint ℓ j) ≫
        μ[(presentationG ℓ).X] =
      sigmaPoint ℓ (i + j) := sorry

/-- The closed subscheme `Φ(s) = 0` in `G`. -/
public noncomputable def presentationKernelCoord (ℓ : ℕ) : Type :=
  presentationGCoord ℓ ⧸
    Ideal.span {Polynomial.aeval (presentationG_s ℓ) (presentationPhi ℓ)}

/-- Evaluation at `0` is the counit of the constant group scheme. -/
public noncomputable def constantZModCounit (ℓ : ℕ) :
    constantZModCoord ℓ →+* cyclotomicIntegers ℓ :=
  Pi.evalRingHom (fun _ : ZMod ℓ => cyclotomicIntegers ℓ) 0

/-- Component inclusion of the identity section of the constant scheme. -/
public theorem constantZModOne_w (ℓ : ℕ) :
    Spec.map (CommRingCat.ofHom (constantZModCounit ℓ)) ≫
        (constantZModOver ℓ).hom =
      (𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ))))).hom :=
  sorry

/-- Unit of the constant group scheme, the inclusion of the `0`-component. -/
public noncomputable def constantZModOne (ℓ : ℕ) :
    𝟙_ (Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ)))) ⟶
      constantZModOver ℓ :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (constantZModCounit ℓ)))
    (constantZModOne_w ℓ)

/-- Inversion on coproduct components sends `i` to `-i`. -/
public noncomputable def constantZModInvHom (ℓ : ℕ) :
    constantZModCoord ℓ →+* constantZModCoord ℓ :=
  RingHom.pi fun i : ZMod ℓ =>
    Pi.evalRingHom (fun _ : ZMod ℓ => cyclotomicIntegers ℓ) (-i)

/-- Inversion of the constant group scheme lies over `Spec A`. -/
public theorem constantZModInv_w (ℓ : ℕ) :
    Spec.map (CommRingCat.ofHom (constantZModInvHom ℓ)) ≫
        (constantZModOver ℓ).hom =
      (constantZModOver ℓ).hom := sorry

/-- Inversion of the constant group scheme. -/
public noncomputable def constantZModInv (ℓ : ℕ) :
    constantZModOver ℓ ⟶ constantZModOver ℓ :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (constantZModInvHom ℓ)))
    (constantZModInv_w ℓ)

/-- Convolution coproduct on `A^(ZMod ℓ)`, sending a function `f` to
`∑_{i,j} f(i + j) • (e_i ⊗ e_j)`. On components this is pairwise addition. -/
public noncomputable def constantZModComul (ℓ : ℕ) [NeZero ℓ] :
    constantZModCoord ℓ →ₐ[cyclotomicIntegers ℓ]
      constantZModCoord ℓ ⊗[cyclotomicIntegers ℓ] constantZModCoord ℓ where
  toFun f :=
    ∑ p : ZMod ℓ × ZMod ℓ,
      f (p.1 + p.2) •
        (Pi.single p.1 (1 : cyclotomicIntegers ℓ) ⊗ₜ[cyclotomicIntegers ℓ]
          Pi.single p.2 (1 : cyclotomicIntegers ℓ))
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- Underlying scheme map of constant-group multiplication: the fibre product
of copies of `Spec A` is identified with `Spec` of the tensor product, then
mapped by convolution. On the `(i, j)`-component this is `Sigma.ι (i + j)`. -/
public noncomputable def constantZModMulLeft (ℓ : ℕ) [NeZero ℓ] :
    (constantZModOver ℓ ⊗ constantZModOver ℓ).left ⟶ (constantZModOver ℓ).left :=
  (pullbackSpecIso (cyclotomicIntegers ℓ) (constantZModCoord ℓ)
        (constantZModCoord ℓ)).hom ≫
    Spec.map (CommRingCat.ofHom (constantZModComul ℓ).toRingHom)

/-- Multiplication of the constant group scheme lies over `Spec A`. -/
public theorem constantZModMul_w (ℓ : ℕ) [NeZero ℓ] :
    constantZModMulLeft ℓ ≫ (constantZModOver ℓ).hom =
      (constantZModOver ℓ ⊗ constantZModOver ℓ).hom := sorry

/-- Multiplication of the constant group scheme. -/
public noncomputable def constantZModMul (ℓ : ℕ) [NeZero ℓ] :
    constantZModOver ℓ ⊗ constantZModOver ℓ ⟶ constantZModOver ℓ :=
  Over.homMk (constantZModMulLeft ℓ) (constantZModMul_w ℓ)

/-- Group-object structure on the finite constant scheme. -/
public noncomputable instance instGrpObjConstantZModOver (ℓ : ℕ) [NeZero ℓ] :
    GrpObj (constantZModOver ℓ) where
  one := constantZModOne ℓ
  mul := constantZModMul ℓ
  inv := constantZModInv ℓ
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The finite constant group scheme `underline(Z / ℓ Z)_A`. -/
public noncomputable def constantZModGroupScheme (ℓ : ℕ) [NeZero ℓ] :
    GroupScheme (Spec (CommRingCat.of (cyclotomicIntegers ℓ))) where
  X := constantZModOver ℓ

/-- Underlying scheme map of the inclusion of the constant group into `G`,
sending the `i`-component to `sigmaPoint i`. -/
public noncomputable def constantInclLeft (ℓ : ℕ) [NeZero ℓ] :
    (constantZModGroupScheme ℓ).X.left ⟶ (presentationG ℓ).X.left :=
  Spec.map
    (CommRingCat.ofHom
      (RingHom.pi fun i : ZMod ℓ => (sigmaPointAlgHom ℓ i).toRingHom))

/-- The constant-group inclusion lies over `Spec A`. -/
public theorem constantInclLeft_w (ℓ : ℕ) [NeZero ℓ] :
    constantInclLeft ℓ ≫ (presentationG ℓ).X.hom =
      (constantZModGroupScheme ℓ).X.hom := sorry

/-- The constant-group inclusion as a morphism over `A`. -/
public noncomputable def constantInclOver (ℓ : ℕ) [NeZero ℓ] :
    (constantZModGroupScheme ℓ).X ⟶ (presentationG ℓ).X :=
  Over.homMk (constantInclLeft ℓ) (constantInclLeft_w ℓ)

/-- The constant-group inclusion preserves units. -/
public theorem constantInclOver_one (ℓ : ℕ) [NeZero ℓ] :
    η[(constantZModGroupScheme ℓ).X] ≫ constantInclOver ℓ =
      η[(presentationG ℓ).X] := sorry

/-- The constant-group inclusion preserves multiplication. -/
public theorem constantInclOver_mul (ℓ : ℕ) [NeZero ℓ] :
    μ[(constantZModGroupScheme ℓ).X] ≫ constantInclOver ℓ =
      (constantInclOver ℓ ⊗ₘ constantInclOver ℓ) ≫ μ[(presentationG ℓ).X] :=
  sorry

/-- The constant-group inclusion is a morphism of monoid objects. -/
public noncomputable instance instIsMonHomConstantInclOver (ℓ : ℕ) [NeZero ℓ] :
    IsMonHom (constantInclOver ℓ) := sorry

/-- The homomorphism `underline(Z / ℓ Z)_A → G` sending `i` to `σ_i`. -/
public noncomputable def constantIncl (ℓ : ℕ) [NeZero ℓ] :
    constantZModGroupScheme ℓ ⟶ presentationG ℓ where
  hom := { hom := constantInclOver ℓ }

/-- The composite of the SES maps is the trivial homomorphism. -/
public theorem constantIncl_comp_presentationHom (ℓ : ℕ) [NeZero ℓ] :
    (constantIncl ℓ ≫ presentationHom ℓ).hom.hom =
      toUnit (constantZModGroupScheme ℓ).X ≫ η[(presentationH ℓ).X] := sorry

/-- The constant group scheme over the cyclotomic integers, embedded by the sections
`sigmaPoint`, is the kernel of the presentation morphism `G ⟶ H`. -/
public theorem presentation_isKernel
    (ℓ : ℕ) [NeZero ℓ] (hℓ : Nat.Prime ℓ) :
    (constantIncl ℓ ≫ presentationHom ℓ).hom.hom =
        toUnit (constantZModGroupScheme ℓ).X ≫ η[(presentationH ℓ).X] ∧
      ∀ {T : Over (Spec (CommRingCat.of (cyclotomicIntegers ℓ)))}
        (g : T ⟶ (presentationG ℓ).X),
        g ≫ (presentationHom ℓ).hom.hom =
            toUnit T ≫ η[(presentationH ℓ).X] →
          ∃! k : T ⟶ (constantZModGroupScheme ℓ).X,
            k ≫ (constantIncl ℓ).hom.hom = g := sorry

/-- The coefficient map defining the cyclotomic presentation morphism `G ⟶ H`
is faithfully flat. -/
public theorem presentationHom_faithfullyFlat
    (ℓ : ℕ) [NeZero ℓ] (hℓ : Nat.Prime ℓ) :
    (Localization.Away.PolynomialPresentation.baseMap (presentationPi ℓ) ℓ (presentationPhi ℓ)
        (presentationPhi_shape ℓ)).toRingHom.FaithfullyFlat := sorry

end AlgebraicGeometry.GroupScheme
