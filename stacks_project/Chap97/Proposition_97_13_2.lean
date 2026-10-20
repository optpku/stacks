/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.PointQuotient
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

/- Proposition 97.13.2: the finite Hilbert stack of a point is equivalent to the
quotient by unit-fixing changes of basis, and is an algebraic stack. -/
@[stacks 05YQ] #check (AlgebraicGeometry.FiniteHilbertStack.comparison_isEquivalence :
  ∀ (d : ℕ) [NeZero d],
    (FiberedCategoryOver.Groupoids.toBasedFunctor
      (AlgebraicGeometry.FiniteHilbertStack.comparison d)).IsEquivalence)

#check (AlgebraicGeometry.FiniteHilbertStack.instAlgebraicStack :
  ∀ (d : ℕ) [NeZero d],
    AlgebraicStack
      (AlgebraicGeometry.FiniteHilbertStack.ofScheme
        AlgebraicGeometry.GLFixOne.specZ d).toGroupoids)
