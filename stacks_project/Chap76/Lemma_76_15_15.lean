/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_15_15_ComparisonPullback
public import stacks_project.Chap76.Lemma_76_15_15_Transitivity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Y Z Z' Y' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
variable (i : Z ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
variable [FormallyUnramified i]
variable (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X))

/- The morphism `Z' ⟶ Y'` of Lemma 76.15.8 on the identity square over `X`. -/
#check
  (comparison iZ fZ iY fY i (𝟙 X) sq : Z' ⟶ Y')

/- Lemma 76.15.15 (1): If `Z ⊂ Z'` and `Y ⊂ Y'` are universal first-order
thickenings over `X`, then the Lemma 76.15.8 comparison gives a morphism
`Z' ⟶ Y'` and `Y ×_{Y'} Z'` is a universal first-order thickening of `Z`
over `Y`. -/
@[stacks 06BF]
#check
  (comparisonPullback_isUniversal iZ fZ iY fY i sq :
    IsUniversalFirstOrder (comparisonPullbackHom iZ fZ iY fY i sq)
      (pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)))

/- Lemma 76.15.15 (2): There is a canonical exact sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` whose maps come from Lemma 76.15.8. -/
@[stacks 06BF]
#check
  (Transitivity.exact_and_epi iZ fZ iY fY i sq :
    (Transitivity.complex iZ fZ iY fY i sq).Exact ∧
      Epi (Transitivity.projection iZ fZ iY fY i sq))
