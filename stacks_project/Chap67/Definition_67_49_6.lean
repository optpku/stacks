/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_49_5_Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 67.49.6: for a scheme `S` and an algebraic space `X` over `S`
satisfying the equivalent conditions of Lemma 67.49.1, recorded as
`HasFiniteIrreducibleComponentsOnCompactOpens X`, the (absolute) normalization
of `X` is the morphism `ν_X = X.normalizationTo : X.normalization ⟶ X`
constructed in Lemma 67.49.5. -/
@[stacks 0BB2] #check
  (@AlgebraicGeometry.AlgebraicSpace.normalizationTo :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      [HasFiniteIrreducibleComponentsOnCompactOpens X] → X.normalization ⟶ X)

/- The domain `X^ν` of the absolute normalization morphism. -/
@[stacks 0BB2] #check
  (@AlgebraicGeometry.AlgebraicSpace.normalization :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      [HasFiniteIrreducibleComponentsOnCompactOpens X] → AlgebraicSpace S)
