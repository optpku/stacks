/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A reduced algebraic stack with quasi-compact inertia projection admits a
dense open substack which is a gerbe over an algebraic space. -/
theorem exists_dense_open_isGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsReduced X]
    [QuasiCompact (FiberedCategoryOver.Groupoids.Inertia.forget.{u + 1, u, u, u + 1} X)] :
    ∃ U : Substack.Open X, IsGerbe (Substack.Open.category U) ∧
      Dense (Substack.Open.pointsSet U) := sorry

end AlgebraicGeometry.AlgebraicStack
