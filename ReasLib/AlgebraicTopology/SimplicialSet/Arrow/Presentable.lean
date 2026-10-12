/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentable arrows of simplicial sets

An arrow of simplicial sets is compact when both endpoints have finitely many nondegenerate
simplices. The cross-universe compactness instance is the primary interface for lifting-property
arguments; finite presentability is retained as its standard same-universe companion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace SSet.Arrow

/-- An arrow of simplicial sets with finite source and target is finitely presentable in the arrow
category. -/
@[stacks 08Q5 "finite-endpoint simplicial-set arrows are finitely presentable"]
instance isFinitelyPresentable (f : CategoryTheory.Arrow SSet.{u})
    [f.left.Finite] [f.right.Finite] :
    IsFinitelyPresentable.{u} f := sorry

/-- The covariant Hom functor of an arrow of simplicial sets with finite source and target
preserves filtered colimits of arbitrary prescribed universe sizes. -/
@[stacks 08Q5 "finite-endpoint simplicial-set arrows are compact"]
instance (priority := 100) compact (f : CategoryTheory.Arrow SSet.{u})
    [f.left.Finite] [f.right.Finite] :
    PreservesFilteredColimitsOfSize.{w, w'}
      (coyoneda.obj (Opposite.op f)) := sorry

end SSet.Arrow
