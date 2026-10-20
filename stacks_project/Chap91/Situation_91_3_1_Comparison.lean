/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FirstOrder

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Thickening.Hom

noncomputable section

universe u

#check (sourceIdealMap :
  {T U : AlgebraicGeometry.RingedSpace.Thickening.{u}} →
    [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening T.hom] →
    [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening U.hom] →
    (g : T ⟶ U) →
      (g.left ^*).obj (AlgebraicGeometry.RingedSpace.Hom.idealModule U.hom) ⟶
        AlgebraicGeometry.RingedSpace.Hom.idealModule T.hom)
