/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback

open CategoryTheory AlgebraicGeometry

universe u

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable (δ : S → ℤ) [IsDimensionFunction δ]
variable (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
variable (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
variable (k : ℤ)

/- Definition 42.14.1: Flat pullback sends a degree-`k` cycle on `Y` to the degree-`k + r`
cycle on `X` obtained by extending the scheme-theoretic inverse-image cycle of each integral
generator additively. -/
@[stacks 02RB] #check
  (AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r k :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k →+
      CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k + (r : ℤ)))

variable (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k)

#check (AlgebraicGeometry.CycleGroup.toAlgebraicCycle_flatPullback δ X Y f r k α :
  AlgebraicGeometry.CycleGroup.toAlgebraicCycle
      (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))
      (AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r k α) =
    AlgebraicGeometry.AlgebraicCycle.flatPullback δ X Y f r (k + (r : ℤ))
      (AlgebraicGeometry.CycleGroup.toAlgebraicCycle
        (Y.hom.relativeDimensionFunction δ) k α))

variable (x : X.left)

#check (AlgebraicGeometry.CycleGroup.flatPullback_apply δ X Y f r k α x :
  AlgebraicGeometry.CycleGroup.toAlgebraicCycle
      (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))
      (AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r k α) x =
    ∑ᶠ y : Y.left,
      AlgebraicGeometry.CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction δ) k α y *
        ((@Scheme.IdealSheafData.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          ((Scheme.PointClosure.reducedStructure y).ideal.comap f.left)
          (X.hom.relativeDimensionFunction δ) (k + (r : ℤ)) :
            AlgebraicCycle.dimensionSubgroup
              (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))) :
          AlgebraicCycle X.left ℤ) x)

end
