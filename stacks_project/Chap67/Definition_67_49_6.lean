module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
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
  (AlgebraicGeometry.AlgebraicSpace.normalizationTo :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      [HasFiniteIrreducibleComponentsOnCompactOpens X] → X.normalization ⟶ X)

/- The domain `X^ν` of the absolute normalization morphism. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.normalization :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      [HasFiniteIrreducibleComponentsOnCompactOpens X] → AlgebraicSpace S)
