/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Closure

/-! Compatibility facade for reduced point closures of algebraic spaces.
The canonical owner is `ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Closure`;
the source-facing Stacks `0CUK` statements live in `Lemma_70_5_4`. -/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.PointClosure.closedSubset :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
      Points X → TopologicalSpace.Closeds (Points X))
