/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Discrete
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry

/- Exercise 111.33.3: a scheme whose underlying topological space is a finite discrete set is affine. -/
@[stacks 03KB] #check (AlgebraicGeometry.Scheme.isAffine_of_finite_discrete :
  ∀ (X : Scheme.{u}) [Finite X] [DiscreteTopology X], IsAffine X)
