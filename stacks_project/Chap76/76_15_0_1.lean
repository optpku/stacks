/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- 76.15.0.1: a first-order thickening `i : Z ⟶ Z'` over `X` via `f : Z' ⟶ X` is
universal when, for every first-order thickening `j : T ⟶ T'` over `X` via
`b : T' ⟶ X` and solid map `a : T ⟶ Z`, there is a unique dotted arrow
`a' : T' ⟶ Z'` with `a ≫ i = j ≫ a'` and `a' ≫ f = b`. -/
@[stacks 0602] #check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder :
    {S : Scheme.{u}} → {X Z Z' : AlgebraicSpace S} → (Z ⟶ Z') → (Z' ⟶ X) → Prop)
