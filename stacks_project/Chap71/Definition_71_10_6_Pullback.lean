/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback

/-! Compatibility facade for the regular-denominator pullback condition. -/

open CategoryTheory AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.PullbacksMeromorphicFunctionsDefined :
    {S : Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ Y) → Prop)
