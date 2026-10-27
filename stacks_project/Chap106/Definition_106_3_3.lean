/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FirstOrderThickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 106.3.3: an algebraic stack `X'` is a first-order thickening of an
algebraic stack `X` if `X` is a closed substack of `X'` and `X ⟶ X'` is a
first-order thickening in the sense of Properties of Stacks, Section 100.3. -/
@[stacks 0BPQ] #check (AlgebraicGeometry.AlgebraicStack.IsFirstOrderSubstack :
  ∀ {S : Scheme.{u}} (X' : GroupoidsOver S) [AlgebraicStack X']
    (P : ObjectProperty X'.total) [P.IsClosedUnderIsomorphisms]
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X'.p))
    [AlgebraicStack (AlgebraicStack.Substack.category X' P h)], Prop)

#check (AlgebraicGeometry.AlgebraicStack.isFirstOrderSubstack_iff_inclusion :
  ∀ {S : Scheme.{u}} (X' : GroupoidsOver S) [AlgebraicStack X']
    (P : ObjectProperty X'.total) [P.IsClosedUnderIsomorphisms]
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X'.p))
    [AlgebraicStack (AlgebraicStack.Substack.category X' P h)],
    AlgebraicStack.IsFirstOrderSubstack X' P h ↔
      AlgebraicStack.IsFirstOrderThickening (AlgebraicStack.Substack.inclusion X' P h))
