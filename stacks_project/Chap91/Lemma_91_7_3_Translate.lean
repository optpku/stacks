/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Torsor
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

universe u

variable {S S' X : RingedSpace.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S}
variable {G : X.Modules} {c : Hom.idealModule t ⟶ (f _*).obj G}

/- Representative translation is determined by the Ext¹ action on compatible classes. -/
#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.translate :
  (Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) → Solution t f G c → Solution t f G c)
