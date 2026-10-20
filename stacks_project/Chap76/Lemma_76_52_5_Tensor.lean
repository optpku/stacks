/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.Tensor

/-!
# Relative perfectness and derived tensor products on algebraic spaces

This file retains the fixed-right derived tensor spelling for source-facing consumers and
imports preservation results for relative perfectness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.DerivedCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}
/-- The fixed-right derived tensor product of objects of `D(𝒪_X)` on an algebraic space. -/
noncomputable abbrev tensorObj {X : AlgebraicSpace S}
    [DerivedTensor.Right.Has (C := X.Modules)] (K M : ModuleDerived X) :
    ModuleDerived X :=
  DerivedTensor.Right.obj K M

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
