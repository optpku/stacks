/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity.FormallyUnramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.ComparisonPullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X : Scheme.{u}} (T U : Thickening.Over X)
  [IsUniversalFirstOrder T] [IsUniversalFirstOrder U]
  (i : T.left.left ⟶ U.left.left) (hi : i ≫ U.left.hom = T.left.hom)

variable [FormallyUnramified i] [FormallyUnramified U.left.hom]

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.ambientComparison T U i hi :
    T.right.left ⟶ U.right.left)

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparisonPullback_isPullback T U i hi :
    IsPullback
      (pullback.fst U.hom.left
        (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.ambientComparison T U i hi))
      (pullback.snd U.hom.left
        (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.ambientComparison T U i hi))
      U.hom.left
      (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.ambientComparison T U i hi))

/- Lemma 37.7.12 (1): for formally unramified `Z ⟶ Y ⟶ X`, the thickening
`Z ⟶ Y ×_[Y'] Z'` induced by chosen universal first-order thickenings over `X` is
universal to first order over `Y`. -/
@[stacks 06AE] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparisonPullback_isUniversal T U i hi :
    AlgebraicGeometry.Thickening.IsUniversalFirstOrder
      (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparisonPullback T U i hi))

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity

variable {X Y Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Y).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})]

variable (i : Z ⟶ Y) (j : Y ⟶ X) [FormallyUnramified i] [FormallyUnramified j]

/- Lemma 37.7.12 (2): for formally unramified `Z ⟶ Y ⟶ X`, the canonical sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` is exact. -/
@[stacks 06AE] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity.exact_and_epi_of_formallyUnramified i j :
    (AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity.complex i j).Exact ∧
      Epi (AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity.projection i j))

end AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity
