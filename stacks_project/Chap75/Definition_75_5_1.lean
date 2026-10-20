/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
import StacksCheckRecall

universe u

/- Definition 75.5.1 -/
@[stacks 071X] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
