/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealMul

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

/- Ideal multiplication and its scalar-restriction comparison. -/
#check (AlgebraicGeometry.RingedSpace.Hom.idealMul :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X'), X'.Modules → X'.Modules)
#check (AlgebraicGeometry.RingedSpace.Hom.homIdealMulEquiv :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] (F' G' : X'.Modules),
    ((i^*).obj F' ⟶ AlgebraicGeometry.RingedSpace.Hom.idealMulRestrict i G') ≃
      (F' ⟶ AlgebraicGeometry.RingedSpace.Hom.idealMul i G'))
