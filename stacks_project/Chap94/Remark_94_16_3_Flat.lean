/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Flat groupoids in algebraic spaces

A groupoid in algebraic spaces is flat when its source and target maps are
flat morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Flatness of a groupoid is a predicate on groupoids in algebraic spaces. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Flat :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, GroupoidAlgebraicSpace B → Prop)
