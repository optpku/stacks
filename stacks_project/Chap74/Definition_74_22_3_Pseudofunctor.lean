/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OverPseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.overPseudofunctor :
  (S : Scheme.{u}) →
    Pseudofunctor (LocallyDiscrete (AlgebraicSpace S)ᵒᵖ) Cat.{u + 1, u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.overPullbackIdIso :
  (W : AlgebraicSpace S) → overPullback (𝟙 W) ≅ 𝟭 (Over W))

#check (AlgebraicGeometry.AlgebraicSpace.overPullbackCompIso :
  (f : B' ⟶ B) → (g : B'' ⟶ B') →
    overPullback (g ≫ f) ≅ overPullback f ⋙ overPullback g)
