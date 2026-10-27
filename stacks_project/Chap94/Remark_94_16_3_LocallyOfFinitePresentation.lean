/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Locally of finite presentation groupoids in algebraic spaces

A groupoid in algebraic spaces is locally of finite presentation when its
source and target maps are locally of finite presentation morphisms of
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Local finite presentation of a groupoid is a predicate on groupoids in algebraic spaces. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.LocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, GroupoidAlgebraicSpace B → Prop)
