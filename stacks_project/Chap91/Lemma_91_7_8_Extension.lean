/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Fiber

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

universe u

/- The tautological first-order thickening defines its canonical extension class. -/
#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.selfExtensionClass :
  ∀ {S S' : RingedSpace.{u}} (t : S ⟶ S') [IsFirstOrderThickening t],
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := S.Modules)).obj NL[t],
      (DerivedCategory.Q (C := S.Modules)).obj
        ((CochainComplex.singleFunctor S.Modules 0).obj (Hom.idealModule t))))
