/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TorsorProjection
public import stacks_project.Chap69.Definition_69_6_2_Koszul

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u
variable {S : Scheme.{u}} {W U : AlgebraicSpace S} (q : W ⟶ U)

#check (AlgebraicGeometry.AlgebraicSpace.sheafInverseImageAdjunction q :
  sheafInverseImage AddCommGrpCat.{u + 1} q ⊣ sheafPushforwardAbelian q)

#check (AlgebraicGeometry.AlgebraicSpace.CharacterSections.inverseImageConstantHom q :
  (sheafInverseImage AddCommGrpCat.{u + 1} q).obj (constantIntegerSheaf U) ⟶
    constantIntegerSheaf W)
