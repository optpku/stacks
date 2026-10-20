/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Fibre degrees of morphisms from schemes to algebraic spaces

The field-valued fibres and uniform degree bounds are defined in
`ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree`.
The imports preserve the chapter's public import surface.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.universallyBoundedFibres_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ X),
    universallyBoundedFibres f ↔
      ∃ n : ℕ, ∀ p : FieldValuedPoint X,
        IsFinite (fieldValuedPointPullbackSnd f p) ∧
          fieldValuedPointPullbackDegree f p ≤ n)
