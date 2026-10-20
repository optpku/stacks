/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 100.6.1: an algebraic stack `X` is quasi-compact if and only if
the topological space `|X|` is quasi-compact. By the immediately following source
lemma, this is equivalent to the existence of a surjective smooth atlas from a
quasi-compact scheme. -/
@[stacks 04YB] #check (AlgebraicGeometry.AlgebraicStack.IsQuasiCompact :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X], Prop)
