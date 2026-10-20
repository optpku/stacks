/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.Transitivity

open CategoryTheory

universe u

#check (AlgebraicGeometry.RingedSpace.transitivityTriangle :
  ∀ {X Y Z : AlgebraicGeometry.RingedSpace.{u}} (_f : X ⟶ Y) (_g : Y ⟶ Z),
    CategoryTheory.Pretriangulated.Triangle (DerivedCategory X.Modules))
