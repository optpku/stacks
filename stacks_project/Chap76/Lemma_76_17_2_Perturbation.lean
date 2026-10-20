/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Pullback
public import stacks_project.Chap76.Lemma_76_17_2_Comparison

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.existsUnique_perturbation :
    ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
      (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
      (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
      [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
      (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
      (ha' : a' ≫ sY' = sX') (sqA : CommSq a iX iY a')
      (θ : (Modules.pullback a).obj (Hom.relativeDifferentials sY) ⟶ Hom.conormalSheaf iX),
      ExistsUnique fun b' : X' ⟶ Y' ↦
        IsPerturbation sY sX' sY' iX iY a a' sqA θ b')
