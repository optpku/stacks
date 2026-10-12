/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap95.Definition_95_18_2

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

namespace AlgebraicGeometry.FiniteHilbertStack

/-- Lemma 97.14.1: if `S` is a scheme and `X` is an algebraic space over `S`, then
the finite Hilbert stack `H_d(X)` is an algebraic stack. -/
@[stacks 05YS, instance]
instance instAlgebraicStack_ofAlgebraicSpace {S : Scheme.{u}}
    (X : AlgebraicSpace S) (d : ℕ) [NeZero d] :
    AlgebraicStack (ofStack X.toGroupoids d).toGroupoids :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
