/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective

/-!
# Approximation of algebraic stacks

The approximation functor of an algebraic stack over a locally Noetherian
scheme is an equivalence, so every formal object is effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The approximation functor of an algebraic stack over a locally Noetherian
scheme is an equivalence of categories. -/
instance approximation.instIsEquivalence {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] :
    (approximation X).IsEquivalence :=
  sorry

/-- Every formal object of an algebraic stack over a locally Noetherian scheme is
effective. -/
instance FormalObject.instIsEffective_algebraicStack {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    (ξ : FormalObject X) :
    FormalObject.IsEffective ξ where
  mem_essImage := CategoryTheory.Functor.EssSurj.mem_essImage (approximation X) ξ

end AlgebraicGeometry.GroupoidsOver
