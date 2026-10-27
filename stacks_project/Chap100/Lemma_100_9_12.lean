/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Opens
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 100.9.12 (1): taking the point image bijects open substacks of an
algebraic stack with open subsets of its point space. -/
@[stacks 06FJ] #check
  (AlgebraicGeometry.AlgebraicStack.Substack.Open.pointsOpens_bijective :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
      Function.Bijective (Substack.Open.pointsOpens (X := X)))

/- Lemma 100.9.12 (2): taking the point image preserves and reflects inclusion
of open substacks. -/
@[stacks 06FJ] #check
  (AlgebraicGeometry.AlgebraicStack.Substack.Open.pointsSet_subset_iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (U V : Substack.Open X),
      Substack.Open.pointsSet U ⊆ Substack.Open.pointsSet V ↔ U.val ≤ V.val)

