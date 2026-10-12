/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle

universe u

#check (AlgebraicGeometry.Scheme.IdealSheafData.associatedCycle :
  {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
    (Z : X.IdealSheafData) → (d : X → ℤ) → (k : ℤ) →
      AlgebraicGeometry.CycleGroup X d k)
