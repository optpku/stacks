/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.RelativeCartier

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.31.1 (1): Cartier Gysin pullback after flat pullback agrees with pullback
along the restriction to the relative effective Cartier divisor. -/
@[stacks 02TR] #check
  (AlgebraicGeometry.ChowGroup.gysin_flatPullback_eq_relativeCartierPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (p : X ⟶ Y) (r : ℕ) [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
      (D : X.left.IdealSheafData) [IsRelativeEffectiveCartierDivisor p.left D]
      (k : ℤ) (α : RelativeChow δ Y (k + 1)),
      AlgebraicGeometry.ChowGroup.cartierGysin δ X D ((k + 1) + (r : ℤ))
          (AlgebraicGeometry.ChowGroup.flatPullback δ X Y p r (k + 1) α) =
        AlgebraicGeometry.ChowGroup.relativeCartierPullback δ X Y p D r (k + 1) α)

/- Lemma 42.31.1 (2): capping a flat pullback with `c₁(D.associatedSheaf)` equals
the pushforward of pullback along the restriction to the divisor. -/
@[stacks 02TR] #check
  (AlgebraicGeometry.ChowGroup.firstChernClassCap_flatPullback_eq_map_relativeCartierPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (p : X ⟶ Y) (r : ℕ) [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
      (D : X.left.IdealSheafData) [IsRelativeEffectiveCartierDivisor p.left D]
      (k : ℤ) (α : RelativeChow δ Y (k + 1)),
      AlgebraicGeometry.ChowGroup.firstChernClassCap δ X D.associatedSheaf
          ((k + 1) + (r : ℤ))
          (AlgebraicGeometry.ChowGroup.flatPullback δ X Y p r (k + 1) α) =
        AlgebraicGeometry.ChowGroup.map δ
          (Over.mk (D.subschemeι ≫ X.hom)) (Over.mk X.hom)
          (Over.homMk D.subschemeι rfl :
            Over.mk (D.subschemeι ≫ X.hom) ⟶ Over.mk X.hom)
          ((k + 1) + (r : ℤ) - 1)
          (AlgebraicGeometry.ChowGroup.relativeCartierPullback
            δ X Y p D r (k + 1) α))
