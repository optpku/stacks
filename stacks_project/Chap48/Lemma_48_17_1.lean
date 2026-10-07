module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.OpenImmersion

open CategoryTheory

universe u

/- Lemma 48.17.1: for an open immersion `j : X ⟶ Y` in
`Scheme.FiniteTypeSeparatedOver S`, the canonical bounded-below upper-shriek functor is
naturally isomorphic to derived pullback along `j`. -/
@[stacks 0AU0] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriekIsoPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S}
      (j : X ⟶ Y) [h_j : AlgebraicGeometry.IsOpenImmersion j.hom.left],
      AlgebraicGeometry.Scheme.Compactification.Of.upperShriek j
          (AlgebraicGeometry.Scheme.Compactification.Of.openImmersion j)
          (𝟭 (AlgebraicGeometry.Scheme.DerivedQCoh.Plus Y.obj.left)) ≅
        @AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackPlus
          _ _ j.hom.left h_j)
