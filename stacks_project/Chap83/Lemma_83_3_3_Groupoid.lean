/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap83.Lemma_83_3_3_BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InvariantBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action.Pullback

/-!
# Invariant re-slicing of groupoids and induced actions

This facade exposes the canonical ReasLib constructions for items (5) and (6) of
Stacks Lemma 83.3.3 (Tag 048G). An invariant morphism `φ : U ⟶ X` regards a groupoid
over `X`; base change to `X'` recovers the invariant base-changed pre-relation.
For an action groupoid, this is the pre-relation of the induced action on `U ×_X X'`.
-/
