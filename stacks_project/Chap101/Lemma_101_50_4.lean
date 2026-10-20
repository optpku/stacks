/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Integral

/-!
# Lemma 101.50.4

Points and integral closed substacks of a decent algebraic stack with
quasi-compact inertia correspond canonically to irreducible closed subsets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.50.4. Singleton closure bijects points with irreducible closed
subsets, and support bijects integral closed substacks with those subsets. -/
@[stacks 0GWE] #check (AlgebraicGeometry.AlgebraicStack.canonicalBijections :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)],
    Function.Bijective
      (irreducibleSetEquivPoints.toEquiv.symm : Points X ≃ IrreducibleCloseds (Points X)) ∧
    Function.Bijective
      (IntegralClosedSubstacks.irreducibleClosed :
        IntegralClosedSubstacks X → IrreducibleCloseds (Points X)) ∧
    (∀ x : Points X,
      (irreducibleSetEquivPoints.toEquiv.symm x : Set (Points X)) = closure {x}) ∧
    (∀ Z : IntegralClosedSubstacks X,
      (IntegralClosedSubstacks.irreducibleClosed Z : Set (Points X)) = Z.pointsSet))

end AlgebraicGeometry.AlgebraicStack
