/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Obstruction

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.existenceObstruction :
  ∀ {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
    (F K : X.Modules) [HasExt.{u} X.Modules]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K),
    CategoryTheory.Abelian.Ext F K 2)
