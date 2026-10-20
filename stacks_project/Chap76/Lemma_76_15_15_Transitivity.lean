/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Transitivity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

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

/- Lemma 76.15.15 (2): There is a canonical exact sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` whose maps come from Lemma 76.15.8. -/
@[stacks 06BF]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Transitivity.exact_and_epi iZ fZ iY fY i sq :
    (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Transitivity.complex iZ fZ iY fY i sq).Exact ∧
      Epi (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Transitivity.projection iZ fZ iY fY i sq))
