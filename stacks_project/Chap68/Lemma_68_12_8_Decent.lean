/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Decent algebraic spaces

The canonical definitions and their API are owned by `ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent`.
This chapter module preserves the original import surface.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsDecent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
