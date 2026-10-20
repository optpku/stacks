/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

variable {S : Scheme.{u}}
variable {Z X Z' X' : AlgebraicSpace S}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
variable [IsImmersion i] [IsImmersion i']
variable (sq : CommSq f i i' g)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.map sq :
    (AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj
      (AlgebraicGeometry.AlgebraicSpace.Hom.conormalSheaf i') ⟶
      AlgebraicGeometry.AlgebraicSpace.Hom.conormalSheaf i)
