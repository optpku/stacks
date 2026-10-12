/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      Matrix.GeneralLinearGroup.det (GeneralLinear.universalMatrix (ULift.{u} ℤ) I) := sorry

/-- The scheme map induced contravariantly by the determinant coordinate-ring map. -/
def left (I : Type u) [Fintype I] [DecidableEq I] :
    (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X.left ⟶
      (𝔾ₘ).X.left :=
  Spec.map (coordinateRingHom I)

/-- The determinant scheme map is compatible with the structure maps to `Spec (ULift ℤ)`. -/
theorem left_w (I : Type u) [Fintype I] [DecidableEq I] :
    left I ≫ (𝔾ₘ).X.hom =
      (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X.hom := sorry

/-- The determinant as a morphism of schemes over `Spec (ULift ℤ)`. -/
def overHom (I : Type u) [Fintype I] [DecidableEq I] :
    (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X ⟶ (𝔾ₘ).toGrp.X :=
  Over.homMk (left I) (left_w I)

/-- The underlying scheme map of `overHom` is the determinant map `left`. -/
theorem overHom_left (I : Type u) [Fintype I] [DecidableEq I] :
    (overHom I).left = left I := sorry

/-- The determinant morphism preserves the canonical monoid-object structures. -/
instance instIsMonHomOverHom (I : Type u) [Fintype I] [DecidableEq I] :
    IsMonHom (overHom I) := sorry

/-- The determinant morphism from the integral general linear group scheme to `𝔾ₘ`. -/
def hom (I : Type u) [Fintype I] [DecidableEq I] :
    GeneralLinear.groupScheme (ULift.{u} ℤ) I ⟶ (𝔾ₘ).toGrp :=
  Grp.homMk'' (overHom I)

/-- The underlying morphism of `hom` is `overHom`. -/
theorem hom_hom_hom (I : Type u) [Fintype I] [DecidableEq I] :
    (hom I).hom.hom = overHom I := sorry

/-- On points, the integral group-scheme morphism `hom` is the matrix determinant. -/
theorem hom_apply (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (g : T ⟶ (GeneralLinear.groupScheme (ULift.{u} ℤ) I).X) :
    MultiplicativeGroup.homEquiv T.left (g.left ≫ (hom I).hom.hom.left) =
      Matrix.GeneralLinearGroup.det (GeneralLinear.HomOver.mulEquiv I T g) := sorry

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
        (GeneralLinear.BaseChange.homMulEquiv (specULiftZIsTerminal.from S) I T g) := sorry

end AlgebraicGeometry.GeneralLinear.Determinant
