/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.AlgebraicStack
import StacksCheckRecall

/-!
# Approximation of algebraic stacks is an equivalence

If `S` is locally Noetherian and `X` is an algebraic stack over `S`, then the
approximation functor from complete local objects of `X` to formal objects of
`X` is an equivalence of categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.9.5: the approximation functor of an algebraic stack over a locally
Noetherian scheme is an equivalence of categories. -/
@[stacks 07X8] #check
  (AlgebraicGeometry.GroupoidsOver.approximation.instIsEquivalence :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X],
      (AlgebraicGeometry.GroupoidsOver.approximation X).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.instIsEffective_algebraicStack :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    (ξ : FormalObject X), FormalObject.IsEffective ξ)

end AlgebraicGeometry.GroupoidsOver
