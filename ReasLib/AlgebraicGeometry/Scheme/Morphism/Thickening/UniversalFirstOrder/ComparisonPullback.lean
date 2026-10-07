module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Comparison

/-!
# Comparison pullbacks of universal first-order thickenings

Chosen universal first-order thickenings over a common base determine a canonical ambient
comparison. Pulling back along this comparison gives a universal first-order thickening over
the intermediate closed scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X : Scheme.{u}} (T U : Thickening.Over X)
  [IsUniversalFirstOrder T] [IsUniversalFirstOrder U]
  (i : T.left.left ⟶ U.left.left) (hi : i ≫ U.left.hom = T.left.hom)

/-- The ambient component `Z' ⟶ Y'` of the canonical map between two chosen universal
first-order thickenings over the same base. -/
noncomputable def ambientComparison : T.right.left ⟶ U.right.left :=
  (lift T (CategoryTheory.Over.homMk i hi)).right.left

/-- The ambient comparison and the prescribed map on the closed parts form a commutative
square. -/
theorem ambientComparison_comm :
    i ≫ U.hom.left = T.hom.left ≫ ambientComparison T U i hi := sorry

/-- The ambient comparison is a morphism over the common base scheme. -/
theorem ambientComparison_over :
    ambientComparison T U i hi ≫ U.right.hom = T.right.hom := sorry

/-- The ambient comparison is uniquely determined by its commutative-square and
over-the-base equations. -/
theorem ambientComparison_unique (k : T.right.left ⟶ U.right.left)
    (hk_comm : i ≫ U.hom.left = T.hom.left ≫ k)
    (hk_over : k ≫ U.right.hom = T.right.hom) :
    k = ambientComparison T U i hi := sorry

/-- The canonical map from the closed scheme `Z` to the fibre product `Y ×_[Y'] Z'`. -/
noncomputable def comparisonPullbackHom :
    T.left.left ⟶ pullback U.hom.left (ambientComparison T U i hi) :=
  pullback.lift i T.hom.left (ambientComparison_comm T U i hi)

/-- The first projection of the canonical map to `Y ×_[Y'] Z'` is `i`. -/
theorem comparisonPullbackHom_fst :
    comparisonPullbackHom T U i hi ≫
        pullback.fst U.hom.left (ambientComparison T U i hi) = i := sorry

/-- The second projection of the canonical map to `Y ×_[Y'] Z'` is the defining map
`Z ⟶ Z'` of `T`. -/
theorem comparisonPullbackHom_snd :
    comparisonPullbackHom T U i hi ≫
        pullback.snd U.hom.left (ambientComparison T U i hi) = T.hom.left := sorry

/-- The canonical map from `Z` to `Y ×_[Y'] Z'` is a thickening. -/
instance comparisonPullbackHom_isThickening :
    IsThickening (comparisonPullbackHom T U i hi) := sorry

/-- The thickening of `Z` over `Y` whose ambient scheme is the canonical fibre product
`Y ×_[Y'] Z'`. -/
noncomputable def comparisonPullback : Thickening.Over U.left.left :=
  MorphismProperty.Arrow.mk
    (CategoryTheory.Over.homMk (comparisonPullbackHom T U i hi)
      (comparisonPullbackHom_fst T U i hi) :
        CategoryTheory.Over.mk i ⟶
          CategoryTheory.Over.mk
            (pullback.fst U.hom.left (ambientComparison T U i hi)))
    (comparisonPullbackHom_isThickening T U i hi)

/-- The closed part of the comparison pullback thickening is `Z ⟶ Y`. -/
theorem comparisonPullback_left :
    (comparisonPullback T U i hi).left = CategoryTheory.Over.mk i := sorry

/-- The ambient part of the comparison pullback thickening is
`Y ×_[Y'] Z' ⟶ Y`. -/
theorem comparisonPullback_right :
    (comparisonPullback T U i hi).right =
      CategoryTheory.Over.mk
        (pullback.fst U.hom.left (ambientComparison T U i hi)) := sorry

/-- The defining scheme morphism of the comparison pullback thickening is the canonical map
from `Z` to `Y ×_[Y'] Z'`. -/
theorem comparisonPullback_hom :
    (CategoryTheory.Over.forget U.left.left).map (comparisonPullback T U i hi).hom =
      comparisonPullbackHom T U i hi := sorry

/-- The ambient scheme of the comparison pullback is the chosen categorical pullback of
`Y ⟶ Y'` and `Z' ⟶ Y'`. -/
theorem comparisonPullback_isPullback :
    IsPullback
      (pullback.fst U.hom.left (ambientComparison T U i hi))
      (pullback.snd U.hom.left (ambientComparison T U i hi))
      U.hom.left (ambientComparison T U i hi) := sorry

/-- If `Z ⟶ Y ⟶ X` is formally unramified, the comparison-pullback thickening induced by
chosen universal first-order thickenings of `Z` and `Y` over `X` is universal over `Y`. -/
instance comparisonPullback_isUniversal [FormallyUnramified i]
    [FormallyUnramified U.left.hom] :
    IsUniversalFirstOrder (comparisonPullback T U i hi) := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
