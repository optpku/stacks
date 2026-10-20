/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced

/-!
# Reduced algebraic stacks

An algebraic stack is reduced when it admits a surjective smooth atlas from a
reduced scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsReduced :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Prop)

namespace IsReduced

#check (AlgebraicGeometry.AlgebraicStack.IsReduced.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsReduced X],
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.IsReduced U.left)

#check (AlgebraicGeometry.AlgebraicStack.IsReduced.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicGeometry.IsReduced U.left],
    IsReduced X)

#check (AlgebraicGeometry.AlgebraicStack.IsReduced.iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsReduced X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicGeometry.IsReduced U.left)

end IsReduced

#check (AlgebraicGeometry.AlgebraicStack.instIsReduced_slice :
  ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsReduced U.left],
    IsReduced (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.isReduced_iff_existsSurjectiveSmooth :
  ∀ {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X],
    IsReduced X ↔
      existsSurjectiveSmooth
        (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) X)

end AlgebraicGeometry.AlgebraicStack
