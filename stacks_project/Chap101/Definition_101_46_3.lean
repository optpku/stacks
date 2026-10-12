/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_46_2_Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Definition 101.46.3: for an algebraic stack `X` satisfying the equivalent
conditions of Lemma 101.46.1, recorded as
`HasFiniteIrreducibleComponentsOnCompactOpens X`, the normalization of `X`
is the morphism `ν = normalizationTo X : normalization X ⟶ X` constructed in
Lemma 101.46.2. -/
@[stacks 0GMK] #check
  (@AlgebraicGeometry.AlgebraicStack.normalizationTo :
    {S : Scheme.{u}} → (X : GroupoidsOver S) →
      [AlgebraicStack X] → [HasFiniteIrreducibleComponentsOnCompactOpens X] →
      normalization X ⟶ X)

/- The domain `X^ν` of the absolute normalization morphism. -/
@[stacks 0GMK] #check
  (@AlgebraicGeometry.AlgebraicStack.normalization :
    {S : Scheme.{u}} → (X : GroupoidsOver S) →
      [AlgebraicStack X] → [HasFiniteIrreducibleComponentsOnCompactOpens X] →
      GroupoidsOver S)
