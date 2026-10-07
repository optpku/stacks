module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct.SelfPower

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 45.8.5 (Voevodsky): for two rational points on a geometrically irreducible
smooth projective scheme over `k`, every sufficiently large self exterior power of
their degree-zero Chow-class difference has finite additive order. -/
@[stacks 0FH9] #check (AlgebraicGeometry.ChowGroup.rationalPointSub_exteriorPower_isTorsion :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.GeometricallyIrreducible X.hom] [AlgebraicGeometry.Smooth X.hom]
    [AlgebraicGeometry.Projective X.hom]
    (x x' : 𝟙_ (AlgebraicGeometry.SchemeOverField k) ⟶ X),
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsOfFinAddOrder
        (AlgebraicGeometry.ChowGroup.selfExteriorPower X
          (AlgebraicGeometry.ChowGroup.rationalPointClass X x -
            AlgebraicGeometry.ChowGroup.rationalPointClass X x') n))
