/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Wedge

open CategoryTheory

universe u

variable {X S : AlgebraicGeometry.RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- This compatibility bridge exposes the complete type of the ringed-space wedge map. -/
#check (AlgebraicGeometry.RingedSpace.DeRham.wedge :
  (f : X ⟶ S) →
    HomologicalComplex.tensorObj
      (AlgebraicGeometry.RingedSpace.DeRham.complex f)
      (AlgebraicGeometry.RingedSpace.DeRham.complex f) ⟶
    AlgebraicGeometry.RingedSpace.DeRham.complex f)
