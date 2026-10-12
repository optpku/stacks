/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap98.Definition_98_9_4_Effective
import Mathlib.Tactic.CrossRefAttribute

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

/-- Lemma 98.9.5: if `S` is a locally Noetherian scheme and `X` is an algebraic
stack over `S`, then the functor `approximation X` of 98.9.3.1 is an
equivalence of categories. -/
@[stacks 07X8, instance]
instance approximation.instIsEquivalence {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] :
    (approximation X).IsEquivalence :=
  sorry

/-- Every formal object of an algebraic stack over a locally Noetherian scheme is
effective. -/
instance FormalObject.instIsEffective_algebraicStack {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    (ξ : FormalObject X) :
    FormalObject.IsEffective ξ :=
  sorry

end AlgebraicGeometry.GroupoidsOver
