/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

universe u v w

variable {Y : Scheme.{u}} (M N : Y.Modules)

#check (SheafOfModules.RingedSite.moduleTensor (𝒪 := Y.𝒪) M N : Y.Modules)

#check (AlgebraicGeometry.RingedSpace.Hom.pullbackTensorIso :
    ∀ {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y) (M N : Y.Modules),
    (AlgebraicGeometry.RingedSpace.Hom.pullback f).obj
        (SheafOfModules.RingedSite.moduleTensor (𝒪 := Y.sheaf) M N) ≅
      SheafOfModules.RingedSite.moduleTensor (𝒪 := X.sheaf)
        ((AlgebraicGeometry.RingedSpace.Hom.pullback f).obj M)
        ((AlgebraicGeometry.RingedSpace.Hom.pullback f).obj N))

