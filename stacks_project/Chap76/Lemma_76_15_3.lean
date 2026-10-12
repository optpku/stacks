/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_15_3_EtaleExtend
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

variable {S : Scheme.{u}}
variable {X Y Z Y' Z' : AlgebraicSpace S}
variable (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (fY' : Y' ⟶ X) (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
variable [Etale fZY] [Etale fZ']
variable (h : IsPullback iZ fZY fZ' iY)

section
variable [IsUniversalFirstOrder iY fY']

/- Lemma 76.15.3 (1): Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be morphisms of
algebraic spaces over `S`, and assume `Z ⟶ Y` is étale. If `Y ⊂ Y'` is a
universal first-order thickening of `Y` over `X`, then the unique étale
morphism `Z' ⟶ Y'` such that `Z = Y ×_{Y'} Z'` (Theorem 76.8.1, via
`spacesEtalePullback_isEquivalence_of_isThickening`, realised by
`etaleExtendHom`) is a universal first-order thickening of `Z` over `X`. -/
@[stacks 0605]
#check
  (IsUniversalFirstOrder.of_etale fZY iY fY' iZ fZ' h :
    IsUniversalFirstOrder iZ (fZ' ≫ fY'))
end

variable [Surjective fZY] [IsFirstOrderThickening iY]
variable [IsUniversalFirstOrder iZ (fZ' ≫ fY')]

/- Lemma 76.15.3 (2): If in addition `Z ⟶ Y` is surjective and
`(Z ⊂ Z') ⟶ (Y ⊂ Y')` is an étale morphism of first-order thickenings over
`X` with `Z'` a universal first-order thickening of `Z` over `X`, then `Y'`
is a universal first-order thickening of `Y` over `X`. -/
@[stacks 0605]
#check
  (IsUniversalFirstOrder.of_etale_surjective fZY iY fY' iZ fZ' h :
    IsUniversalFirstOrder iY fY')
