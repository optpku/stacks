/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Algebraic
import StacksCheckRecall

/-!
# Lemma 97.14.1

If `S` is a scheme and `X` is an algebraic space over `S`, then the finite
Hilbert stack `H_d(X)` is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

noncomputable section

universe u

/- Lemma 97.14.1: if `S` is a scheme and `X` is an algebraic space over `S`, then
the finite Hilbert stack `H_d(X)` is an algebraic stack. -/
@[stacks 05YS]
#check (AlgebraicGeometry.FiniteHilbertStack.instAlgebraicStack_ofAlgebraicSpace :
  {S : Scheme.{u}} → (X : AlgebraicSpace S) → (d : ℕ) → [NeZero d] →
    AlgebraicStack (ofStack X.toGroupoids d).toGroupoids)
