/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.ClosedImmersion
import StacksCheckRecall

/-!
# Closed immersions of algebraic spaces are proper

A closed immersion of algebraic spaces over a scheme `S` is a proper morphism
of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.40.5: A closed immersion of algebraic spaces is a proper morphism
of algebraic spaces. -/
@[stacks 04XZ] #check (AlgebraicGeometry.AlgebraicSpace.Proper.of_isClosedImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion f],
    AlgebraicGeometry.AlgebraicSpace.Proper f)
