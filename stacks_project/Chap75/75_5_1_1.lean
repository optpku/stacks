/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Comparison
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- 75.5.1.1: the canonical functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 08F1] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparison X :
    DerivedCategory (QCoh X) ⥤ DerivedQCoh X)
