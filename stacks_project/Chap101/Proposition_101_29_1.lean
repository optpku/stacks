/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.DenseOpen
import StacksCheckRecall

/-!
# Dense open gerbe in a reduced algebraic stack

A reduced algebraic stack whose inertia morphism is quasi-compact admits a
dense open substack which is a gerbe over some algebraic space.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Proposition 101.29.1: A reduced algebraic stack with quasi-compact inertia
projection admits a dense open substack which is a gerbe. -/
@[stacks 06RC] #check
  (AlgebraicGeometry.AlgebraicStack.exists_dense_open_isGerbe :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsReduced X]
      [QuasiCompact (FiberedCategoryOver.Groupoids.Inertia.forget.{u + 1, u, u, u + 1} X)],
      ∃ U : Substack.Open X, IsGerbe (Substack.Open.category U) ∧
        Dense (Substack.Open.pointsSet U))

end AlgebraicGeometry.AlgebraicStack
