/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle

universe u

#check (AlgebraicGeometry.Scheme.IdealSheafData.associatedCycle :
  {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
    (Z : X.IdealSheafData) → (d : X → ℤ) → (k : ℤ) →
      AlgebraicGeometry.CycleGroup X d k)
