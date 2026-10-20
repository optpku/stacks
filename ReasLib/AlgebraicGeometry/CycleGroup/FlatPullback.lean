/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback

/-!
# Flat pullback of cycles of fixed dimension

This file defines flat pullback as an additive homomorphism between cycle groups of fixed
relative dimension and records its underlying-cycle and coefficient formulas.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- The underlying value of flat pullback from degree-`k` cycles to degree-`k + r` cycles. -/
noncomputable def flatPullbackValue
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k + (r : ℤ)) :=
  ⟨AlgebraicCycle.flatPullback δ X Y f r (k + (r : ℤ))
      (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) k α),
    AlgebraicCycle.flatPullback_mem_dimensionSubgroup
      δ X Y f r (k + (r : ℤ))
        (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) k α)⟩

/-- Flat pullback sends the zero degree-`k` cycle to zero. -/
theorem flatPullbackValue_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) :
    flatPullbackValue δ X Y f r k 0 = 0 := sorry

/-- Flat pullback preserves addition of degree-`k` cycles. -/
theorem flatPullbackValue_add
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (a b : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k) :
    flatPullbackValue δ X Y f r k (a + b) =
      flatPullbackValue δ X Y f r k a + flatPullbackValue δ X Y f r k b := sorry

/-- Flat pullback as an additive homomorphism from degree-`k` cycles to degree-`k + r`
cycles. -/
noncomputable def flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k →+
      CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k + (r : ℤ)) where
  toFun := flatPullbackValue δ X Y f r k
  map_zero' := flatPullbackValue_zero δ X Y f r k
  map_add' := flatPullbackValue_add δ X Y f r k

/-- Forgetting the grading after flat pullback gives the underlying pullback of algebraic
cycles. -/
theorem toAlgebraicCycle_flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))
        (flatPullback δ X Y f r k α) =
      AlgebraicCycle.flatPullback δ X Y f r (k + (r : ℤ))
        (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) k α) := sorry

/-- The coefficient of a flat pullback is the locally finite sum of the input coefficients
times the associated cycles of the scheme-theoretic inverse images. -/
theorem flatPullback_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k)
    (x : X.left) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))
        (flatPullback δ X Y f r k α) x =
      ∑ᶠ y : Y.left,
        toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) k α y *
          ((@Scheme.IdealSheafData.associatedCycle X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            ((Scheme.PointClosure.reducedStructure y).ideal.comap f.left)
            (X.hom.relativeDimensionFunction δ) (k + (r : ℤ)) :
              AlgebraicCycle.dimensionSubgroup
                (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))) :
            AlgebraicCycle X.left ℤ) x := sorry

end AlgebraicGeometry.CycleGroup
