/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap76.Lemma_76_5_3_Map
public import stacks_project.Chap76.Lemma_76_18_1_Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Sections

/-!
# Compatible local deformations of maps of algebraic spaces

Typed compatibility check for the set of compatible local deformations on the
spaces-étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
variable (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (A : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.sections sX' sY' iX iY a A :
  (U' : spacesEtaleSite X') → Set (U'.left ⟶ Y'))
