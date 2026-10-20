/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.DifferenceConstruction

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.Thickening
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
noncomputable section
universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.differenceDerivation :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB),
    Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.differenceParameter :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB),
    (Modules.pullback a).obj (Hom.relativeDifferentials sY) ⟶ Hom.conormalSheaf iX)
