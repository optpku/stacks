/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Differentials.Transitivity

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The conormal-differentials short complex is available with the same geometric
argument order to consumers of this module. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.Transitivity.complex :
    ∀ {S : Scheme.{u}} {X Y Z ZX ZY : AlgebraicSpace S}
      (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y) (f : X ⟶ Y)
      [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
      [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)],
      CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f → ShortComplex Z.Modules)
