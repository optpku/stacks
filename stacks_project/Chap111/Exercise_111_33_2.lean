/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.TwoPoints
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.33.2: a scheme whose underlying topological space has two points is affine. -/
@[stacks 028Q] #check (AlgebraicGeometry.isAffine_of_natCard_eq_two :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, Nat.card X = 2 → AlgebraicGeometry.IsAffine X)
