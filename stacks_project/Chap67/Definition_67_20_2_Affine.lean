/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Affine morphisms of algebraic spaces

This module retains the historical source imports and checks the shared affine
algebraic-space API for downstream consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- The shared affine API remains available through this typed compatibility check. -/
#check (AlgebraicGeometry.AlgebraicSpace.Affine :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
