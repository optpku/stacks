/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteComponents

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.46.1: For an algebraic stack, the smooth-atlas, smooth-scheme,
smooth-algebraic-space, and quasi-compact smooth-stack conditions for finiteness
of irreducible components are equivalent. -/
@[stacks 0GMI]
#check (AlgebraicGeometry.AlgebraicStack.HasFiniteIrreducibleComponentsOnCompactOpens.tfae :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    List.TFAE
      [existsSurjectiveSmooth
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallSmooth
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallSmoothSpaceFiniteComponents X,
        finiteIrreducibleComponentsOnSmoothCompact X])
