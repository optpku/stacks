/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback

/-!
# Flat pullback along a displayed scheme morphism

Flat pullback can be expressed using structure maps and a commuting triangle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Flat pullback along a scheme morphism over a base sends degree-`k` cycles
to degree-`k + d` cycles. -/
noncomputable def flatPullbackAlong
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (φ : X ⟶ Y) (hφ : φ ≫ pY = pX) (d : ℕ)
    [Flat φ] [Scheme.Hom.RelativeDimension φ d] (k : ℤ) :
    CycleGroup Y (pY.relativeDimensionFunction δ) k →+
      CycleGroup X (pX.relativeDimensionFunction δ) (k + (d : ℤ)) :=
  @flatPullback S _ δ _ (Over.mk pX) (Over.mk pY)
    (show LocallyOfFiniteType (Over.mk pX).hom from inferInstanceAs (LocallyOfFiniteType pX))
    (show LocallyOfFiniteType (Over.mk pY).hom from inferInstanceAs (LocallyOfFiniteType pY))
    (Over.homMk φ hφ) d
    (show Flat (Over.homMk φ hφ : Over.mk pX ⟶ Over.mk pY).left from
      inferInstanceAs (Flat φ))
    (show Scheme.Hom.RelativeDimension
        (Over.homMk φ hφ : Over.mk pX ⟶ Over.mk pY).left d from
      inferInstanceAs (Scheme.Hom.RelativeDimension φ d)) k

/-- A coefficient of flat pullback is the locally finite sum of the original
coefficients multiplied by the cycles of their scheme-theoretic inverse images. -/
theorem flatPullbackAlong_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (φ : X ⟶ Y) (hφ : φ ≫ pY = pX) (d : ℕ)
    [Flat φ] [Scheme.Hom.RelativeDimension φ d] (k : ℤ)
    (α : CycleGroup Y (pY.relativeDimensionFunction δ) k) (x : X) :
    toAlgebraicCycle (pX.relativeDimensionFunction δ) (k + (d : ℤ))
        (flatPullbackAlong δ pX pY φ hφ d k α) x =
      ∑ᶠ y : Y,
        toAlgebraicCycle (pY.relativeDimensionFunction δ) k α y *
          ((@Scheme.IdealSheafData.associatedCycle X
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            ((Scheme.PointClosure.reducedStructure y).ideal.comap φ)
            (pX.relativeDimensionFunction δ) (k + (d : ℤ)) :
              AlgebraicCycle.dimensionSubgroup
                (pX.relativeDimensionFunction δ) (k + (d : ℤ))) :
            AlgebraicCycle X ℤ) x := by
  exact @flatPullback_apply S _ δ _ (Over.mk pX) (Over.mk pY)
    (inferInstanceAs (LocallyOfFiniteType pX))
    (inferInstanceAs (LocallyOfFiniteType pY)) (Over.homMk φ hφ) d
    (inferInstanceAs (Flat φ)) (inferInstanceAs (Scheme.Hom.RelativeDimension φ d)) k α x

end AlgebraicGeometry.CycleGroup
