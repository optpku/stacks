/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Moduli
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
variable (C : ObjectProperty (AlgebraicSpace S))

/- Definition 106.12.1 (1): a morphism `f : X ⟶ Y` from an algebraic stack to an
algebraic space is a categorical moduli space if any morphism `X ⟶ W` to an
algebraic space factors uniquely through `f`. -/
#check (AlgebraicGeometry.AlgebraicStack.IsCategoricalModuliSpace f : Prop)

/- Definition 106.12.1 (2): a morphism `f : X ⟶ Y` from an algebraic stack to an
algebraic space is a uniform categorical moduli space if for any flat morphism
`Y' ⟶ Y` of algebraic spaces the base change `pullbackSnd f h : Y' ×_Y X ⟶ Y'`
is a categorical moduli space. -/
#check (AlgebraicGeometry.AlgebraicStack.IsUniformCategoricalModuliSpace f : Prop)

/- Definition 106.12.1 (3): a morphism `f : X ⟶ Y` from an algebraic stack to an
algebraic space is a categorical moduli space in a full subcategory `C` of
algebraic spaces if `Y` lies in `C` and any morphism `X ⟶ W` with `W` in `C`
factors uniquely through `f`. -/
#check (AlgebraicGeometry.AlgebraicStack.IsCategoricalModuliSpaceIn C f : Prop)

/- Definition 106.12.1 (4): a morphism `f : X ⟶ Y` from an algebraic stack to an
algebraic space is a uniform categorical moduli space in a full subcategory `C`
of algebraic spaces if `Y` lies in `C` and for every flat morphism `Y' ⟶ Y` in
`C` the base change `pullbackSnd f h : Y' ×_Y X ⟶ Y'` is a categorical moduli
space in `C`. -/
#check (AlgebraicGeometry.AlgebraicStack.IsUniformCategoricalModuliSpaceIn C f : Prop)
