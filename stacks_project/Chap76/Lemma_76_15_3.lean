module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Etale
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.15.3 (1): Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be morphisms of
algebraic spaces over `S`, and assume `Z ⟶ Y` is étale. If `Y ⊂ Y'` is a
universal first-order thickening of `Y` over `X`, then the unique étale
morphism `Z' ⟶ Y'` such that `Z = Y ×_{Y'} Z'` (Theorem 76.8.1, via
`spacesEtalePullback_isEquivalence_of_isThickening`, realised by
`etaleExtendHom`) is a universal first-order thickening of `Z` over `X`. -/
@[stacks 0605]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.of_etale :
    ∀ {S : Scheme.{u}} {X Y Z Y' Z' : AlgebraicSpace S}
      (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (fY' : Y' ⟶ X) (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
      [Etale fZY] [IsUniversalFirstOrder iY fY'] [Etale fZ'],
      IsPullback iZ fZY fZ' iY → IsUniversalFirstOrder iZ (fZ' ≫ fY'))

/- Lemma 76.15.3 (2): If in addition `Z ⟶ Y` is surjective and
`(Z ⊂ Z') ⟶ (Y ⊂ Y')` is an étale morphism of first-order thickenings over
`X` with `Z'` a universal first-order thickening of `Z` over `X`, then `Y'`
is a universal first-order thickening of `Y` over `X`. -/
@[stacks 0605]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.of_etale_surjective :
    ∀ {S : Scheme.{u}} {X Y Z Y' Z' : AlgebraicSpace S}
      (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (fY' : Y' ⟶ X) (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
      [Etale fZY] [Surjective fZY] [IsFirstOrderThickening iY] [Etale fZ']
      [IsUniversalFirstOrder iZ (fZ' ≫ fY')],
      IsPullback iZ fZY fZ' iY → IsUniversalFirstOrder iY fY')
