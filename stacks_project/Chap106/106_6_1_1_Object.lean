/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Object
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap106.Definition_106_3_1_Thickening

/-!
# Objects of the category of lifts of algebraic stacks

An object of the category of lifts along a thickening of algebraic stacks is a
system of algebraic spaces and maps forming a 2-cartesian square over the
thickening, with an étale map to the given algebraic space and a smooth map
from the thickened space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Lift.Object :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x], Type (u + 1))
