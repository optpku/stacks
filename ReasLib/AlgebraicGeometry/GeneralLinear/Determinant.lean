/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme

/-!
# The determinant morphism of group schemes

This module constructs the determinant morphism from the integral general linear group scheme
to the multiplicative group scheme and transports it to arbitrary base schemes.
-/

@[expose] public section

open CategoryTheory
open MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GeneralLinear.Determinant

/-- The coordinate-ring map classifying determinant on the integral general linear scheme. -/
def coordinateRingHom (I : Type u) [Fintype I] [DecidableEq I] :
    CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶
      CommRingCat.of (GeneralLinear.coordinateRing (ULift.{u} ℤ) I) :=
  MultiplicativeGroup.ringHomOfUnit
    (CommRingCat.of (GeneralLinear.coordinateRing (ULift.{u} ℤ) I))
    (Matrix.GeneralLinearGroup.det (GeneralLinear.universalMatrix (ULift.{u} ℤ) I))

/-- The Laurent generator maps to the determinant of the universal invertible matrix. -/
theorem coordinateRingHom_T (I : Type u) [Fintype I] [DecidableEq I] :
    coordinateRingHom I (LaurentPolynomial.T 1) =
      Matrix.GeneralLinearGroup.det (GeneralLinear.universalMatrix (ULift.{u} ℤ) I) := by
  change (LaurentPolynomial.eval₂ _ _) (LaurentPolynomial.T 1) = _
  simp only [LaurentPolynomial.eval₂_T, zpow_one]

/-- The scheme map induced contravariantly by the determinant coordinate-ring map. -/
def left (I : Type u) [Fintype I] [DecidableEq I] :
    (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X.left ⟶
      (𝔾ₘ).X.left :=
  Spec.map (coordinateRingHom I)

/-- The determinant scheme map is compatible with the structure maps to `Spec (ULift ℤ)`. -/
theorem left_w (I : Type u) [Fintype I] [DecidableEq I] :
    left I ≫ (𝔾ₘ).X.hom =
      (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X.hom := by
  change Spec.map (coordinateRingHom I) ≫
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C) =
    Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ)
        (GeneralLinear.coordinateRing (ULift.{u} ℤ) I)))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact (CommRingCat.isInitial).hom_ext _ _

/-- The determinant as a morphism of schemes over `Spec (ULift ℤ)`. -/
def overHom (I : Type u) [Fintype I] [DecidableEq I] :
    (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X ⟶ (𝔾ₘ).toGrp.X :=
  Over.homMk (left I) (left_w I)

/-- The underlying scheme map of `overHom` is the determinant map `left`. -/
theorem overHom_left (I : Type u) [Fintype I] [DecidableEq I] :
    (overHom I).left = left I := rfl

private theorem overHom_apply (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (g : T ⟶ (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X) :
    MultiplicativeGroup.homOverMulEquiv T (g ≫ overHom I) =
      Matrix.GeneralLinearGroup.det (GeneralLinear.HomOver.mulEquiv I T g) := by
  rw [MultiplicativeGroup.homOverMulEquiv_apply]
  apply Units.ext
  change (Scheme.homToSpecGlobalSectionsEquiv T.left _
      (g.left ≫ Spec.map (coordinateRingHom I))) (LaurentPolynomial.T 1) =
    (Matrix.GeneralLinearGroup.det
      (GeneralLinear.CoordinateRing.matrixOfHom I
        (Scheme.homToSpecGlobalSectionsEquiv T.left _ g.left).hom) : Γ(T.left, ⊤))
  rw [Scheme.homToSpecGlobalSectionsEquiv_apply,
    Scheme.homToSpecGlobalSectionsEquiv_apply]
  rw [Scheme.Hom.comp_appTop]
  rw [← Category.assoc]
  erw [← Scheme.ΓSpecIso_inv_naturality (coordinateRingHom I)]
  change (Scheme.Hom.appTop (Over.Hom.left g))
      ((coordinateRingHom I ≫ (Scheme.ΓSpecIso
        (CommRingCat.of (GeneralLinear.coordinateRing (ULift.{u} ℤ) I))).inv)
        (LaurentPolynomial.T 1)) = _
  rw [CommRingCat.comp_apply]
  rw [coordinateRingHom_T]
  rw [GeneralLinear.CoordinateRing.matrixOfHom, Matrix.GeneralLinearGroup.map_det]
  rfl

/-- The determinant morphism preserves the canonical monoid-object structures. -/
instance instIsMonHomOverHom (I : Type u) [Fintype I] [DecidableEq I] :
    IsMonHom (overHom I) := by
  constructor
  · apply (MultiplicativeGroup.homOverMulEquiv _).injective
    rw [overHom_apply]
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact ((Matrix.GeneralLinearGroup.det.comp
      (GeneralLinear.HomOver.mulEquiv I _).toMonoidHom).map_one).trans
        (MultiplicativeGroup.homOverMulEquiv _).map_one.symm
  · apply (MultiplicativeGroup.homOverMulEquiv _).injective
    rw [overHom_apply]
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, MonObj.comp_mul]
    erw [(GeneralLinear.HomOver.mulEquiv I _).map_mul, map_mul]
    rw [← overHom_apply, ← overHom_apply]
    rw [tensorHom_fst, tensorHom_snd]
    exact ((MultiplicativeGroup.homOverMulEquiv _).map_mul _ _).symm

/-- The determinant morphism from the integral general linear group scheme to `𝔾ₘ`. -/
def hom (I : Type u) [Fintype I] [DecidableEq I] :
    GeneralLinear.groupScheme (ULift.{u} ℤ) I ⟶ (𝔾ₘ).toGrp :=
  Grp.homMk'' (overHom I)

/-- The underlying morphism of `hom` is `overHom`. -/
theorem hom_hom_hom (I : Type u) [Fintype I] [DecidableEq I] :
    (hom I).hom.hom = overHom I := rfl

/-- On points, the integral group-scheme morphism `hom` is the matrix determinant. -/
theorem hom_apply (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (g : T ⟶ (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X) :
    MultiplicativeGroup.homEquiv T.left (g.left ≫ (hom I).hom.hom.left) =
      Matrix.GeneralLinearGroup.det (GeneralLinear.HomOver.mulEquiv I T g) := by
  have h := overHom_apply I T g
  rw [MultiplicativeGroup.homOverMulEquiv_apply] at h
  exact h

/-- Base change of the determinant morphism to a scheme `S`. -/
def baseChange (S : Scheme.{u}) (I : Type u) [Fintype I] [DecidableEq I] :
    GeneralLinear.baseChange (specULiftZIsTerminal.from S) I ⟶
      (𝔾ₘ[S]).toGrp :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.map (hom I)

/-- On relative points, the base-changed morphism is the matrix determinant. -/
theorem baseChange_apply (S : Scheme.{u}) (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over S) (g : T ⟶ (GeneralLinear.baseChange
      (specULiftZIsTerminal.from S) I).X) :
    MultiplicativeGroup.baseChangeHomEquiv S T
        (g ≫ (baseChange S I).hom.hom) =
      Matrix.GeneralLinearGroup.det
        (GeneralLinear.BaseChange.homMulEquiv (specULiftZIsTerminal.from S) I T g) := by
  unfold MultiplicativeGroup.baseChangeHomEquiv
  rw [Equiv.trans_apply, MultiplicativeGroup.baseChangeHomEquivAbsolute_apply]
  rw [GeneralLinear.BaseChange.homMulEquiv_apply, GeneralLinear.HomOver.mulEquiv_apply]
  change (MultiplicativeGroup.homOverEquiv ((Over.map
      (specULiftZIsTerminal.from S)).obj T))
      (((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv T
          (𝔾ₘ).toGrp.toMon.X).symm
        (g ≫ (Over.pullback (specULiftZIsTerminal.from S)).map
          (hom I).hom.hom)) = _
  have hnat := Adjunction.homEquiv_naturality_right_symm
    (Over.mapPullbackAdj (specULiftZIsTerminal.from S)) g (hom I).hom.hom
  erw [hnat]
  unfold GeneralLinear.BaseChange.pullbackHomEquiv
  change MultiplicativeGroup.homEquiv ((Over.map
      (specULiftZIsTerminal.from S)).obj T).left
      ((((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv T
          (groupScheme (ULift.{u} ℤ) I).X).symm g).left ≫
        (hom I).hom.hom.left) = _
  exact hom_apply I ((Over.map (specULiftZIsTerminal.from S)).obj T)
    (((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv T
      (groupScheme (ULift.{u} ℤ) I).X).symm g)

end AlgebraicGeometry.GeneralLinear.Determinant
