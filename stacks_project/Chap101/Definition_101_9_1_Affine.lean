/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine

/-!
# Affine morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is affine when every representing morphism
of algebraic spaces `fy : Fy ⟶ ofOver U` is an affine morphism of algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- The shared affine API remains available through this typed compatibility check. -/
#check (AlgebraicGeometry.Groupoids.Hom.Affine :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S},
    (X ⟶ Y) → Prop)
