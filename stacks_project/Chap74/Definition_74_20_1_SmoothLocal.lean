/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal

/-!
# Smooth locality on source-and-target

A morphism property of algebraic spaces over a scheme `S` is smooth local on
source-and-target when it is stable under smooth precomposition and smooth base
change, and can be checked on pointwise commutative squares with smooth vertical
arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

noncomputable section

#check
  (AlgebraicGeometry.AlgebraicSpace.existsSmoothSquareAt :
    {S : AlgebraicGeometry.Scheme.{u}} →
      CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S) →
        {X Y : AlgebraicGeometry.AlgebraicSpace S} →
          (X ⟶ Y) → AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
