/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Inertia
import StacksCheckRecall

/-!
# When an algebraic stack is a gerbe

An algebraic stack is a gerbe if and only if its canonical inertia morphism is
flat and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicStack

/- Proposition 101.28.9: an algebraic stack is a gerbe if and only if its
canonical inertia morphism is flat and locally of finite presentation. -/
@[stacks 06QJ] #check
  (AlgebraicGeometry.AlgebraicStack.isGerbe_iff_inertia_flat_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsGerbe X ↔
        Flat (FiberedCategoryOver.Groupoids.Inertia.forget.{u + 1, u, u, u + 1} X) ∧
          LocallyOfFinitePresentation
            (FiberedCategoryOver.Groupoids.Inertia.forget.{u + 1, u, u, u + 1} X))
