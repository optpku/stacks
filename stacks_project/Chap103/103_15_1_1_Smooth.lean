/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-! # Smooth morphisms of algebraic stacks -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Smooth :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicStack.smooth_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Smooth f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h)

#check (AlgebraicGeometry.AlgebraicStack.Smooth.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    Smooth (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Smooth.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Smooth h)
