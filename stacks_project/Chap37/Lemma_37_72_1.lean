/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

/- Lemma 37.72.1: For a proper morphism whose fiber over `y` has dimension at most one,
vanishing of the first higher direct image of the structure sheaf after a cartesian base
change through a point above `y` implies vanishing of `H¹(X_y, 𝒪_{X_y})`. -/
@[stacks 0E7F] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.fiberH1_isZero_of_baseChange :
    ∀ {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞) →
      (g' : X' ⟶ X) → (f' : X' ⟶ Y') → (g : Y' ⟶ Y) →
      IsPullback g' f' f g → (y' : Y') → g y' = y →
      IsZero
          (RingedSpace.Hom.higherDirectImageModule f'.toShHom
            (SheafOfModules.unit X'.ringCatSheaf) 1) →
        IsZero
          (Scheme.Modules.cohomology
            (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))

#check
  (AlgebraicGeometry.Scheme.HigherDirectImage.fiberH1_isZero_of_degreeOne_isZero :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞) →
      IsZero
          (RingedSpace.Hom.higherDirectImageModule f.toShHom
            (SheafOfModules.unit X.ringCatSheaf) 1) →
        IsZero
          (Scheme.Modules.cohomology
            (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1))

end AlgebraicGeometry.Scheme.HigherDirectImage
