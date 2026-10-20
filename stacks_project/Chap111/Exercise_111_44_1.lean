/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.NonkillableClass
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.44.1: the projective line over a field, the invertible ideal sheaf of
its zero and infinity points, and the boundary of their indicator section give a
cohomology class that remains nonzero under every finite surjective scheme morphism. -/
@[stacks 0DB4] #check
  (AlgebraicGeometry.ProjectiveLine.NonkillableClass.cohomologyPullback_ne_zero :
    ∀ (k : Type u) [Field k] {Y : Scheme.{u}} (π : Y ⟶ ProjectiveLine.scheme k)
      [IsFinite π] [Surjective π],
      Scheme.Hom.cohomologyPullback (ProjectiveLine.toSpec k) π
        (ProjectiveLine.NonkillableClass.lineBundle k) 1
        (ProjectiveLine.NonkillableClass.xi k) ≠ 0)
