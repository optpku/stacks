/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Radicial

/-!
# Radicial morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme is radicial when every field-valued
fibre, after reduction, is empty or the spectrum of a purely inseparable extension
of the source field. This is strictly stronger than universal injectivity.
-/

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Radicial :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
