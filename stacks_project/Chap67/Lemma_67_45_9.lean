/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Proper
import StacksCheckRecall

/-!
# Finite morphisms of algebraic spaces versus affine proper morphisms

A morphism of algebraic spaces is finite if and only if it is affine and
proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.45.9: A morphism of algebraic spaces is finite if and only if it
is affine and proper. -/
@[stacks 04NZ] #check (AlgebraicGeometry.AlgebraicSpace.IsFinite.iff_proper_and_affine :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.IsFinite f ↔
      AlgebraicGeometry.AlgebraicSpace.Proper f ∧ AlgebraicGeometry.AlgebraicSpace.Affine f)
