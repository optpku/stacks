module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap76.Lemma_76_15_8_Comparison

/-!
# Comparison pullbacks of universal first-order thickenings of algebraic spaces

Chosen universal first-order thickenings of `Z` and `Y` over `X` determine a
canonical Lemma 76.15.8 comparison `Z' ⟶ Y'`. The fibre product `Y ×_{Y'} Z'`
carries a closed immersion of `Z` which is a universal first-order thickening
of `Z` over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

variable {S : Scheme.{u}} {X Y Z Z' Y' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
variable (i : Z ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
variable (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X))

/-- The fibre product `Y ×_{Y'} Z'` of the closed immersion `Y ⊂ Y'` with the
Lemma 76.15.8 comparison morphism `Z' ⟶ Y'`. -/
noncomputable def comparisonPullback : AlgebraicSpace S :=
  pullback iY (comparison iZ fZ iY fY i (𝟙 X) sq)

/-- `comparisonPullback` is the chosen categorical fibre product of `Y ⟶ Y'` and
the comparison `Z' ⟶ Y'`. -/
theorem comparisonPullback_eq :
    comparisonPullback iZ fZ iY fY i sq =
      pullback iY (comparison iZ fZ iY fY i (𝟙 X) sq) :=
  sorry

/-- The canonical closed immersion of `Z` into the fibre product `Y ×_{Y'} Z'`. -/
noncomputable def comparisonPullbackHom : Z ⟶ comparisonPullback iZ fZ iY fY i sq :=
  pullback.lift i iZ (comparison_comp iZ fZ iY fY i (𝟙 X) sq)

/-- `comparisonPullbackHom` is the mediating map of `i : Z ⟶ Y` and `Z ⊂ Z'` into
the fibre product. -/
theorem comparisonPullbackHom_eq :
    comparisonPullbackHom iZ fZ iY fY i sq =
      pullback.lift i iZ (comparison_comp iZ fZ iY fY i (𝟙 X) sq) :=
  sorry

/-- The first projection of `comparisonPullbackHom` recovers `i : Z ⟶ Y`. -/
theorem comparisonPullbackHom_fst :
    comparisonPullbackHom iZ fZ iY fY i sq ≫
        pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq) =
      i :=
  sorry

/-- The second projection of `comparisonPullbackHom` recovers `Z ⊂ Z'`. -/
theorem comparisonPullbackHom_snd :
    comparisonPullbackHom iZ fZ iY fY i sq ≫
        pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) =
      iZ :=
  sorry

/-- The projections of `Y ×_{Y'} Z'` exhibit it as the fibre product of `Y ⊂ Y'`
and the comparison `Z' ⟶ Y'`. -/
theorem comparisonPullback_isPullback :
    IsPullback
      (pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq))
      (pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq))
      iY (comparison iZ fZ iY fY i (𝟙 X) sq) :=
  sorry

/-- The canonical map `Z ⟶ Y ×_{Y'} Z'` is a first-order thickening. -/
instance comparisonPullbackHom_isFirstOrderThickening :
    IsFirstOrderThickening (comparisonPullbackHom iZ fZ iY fY i sq) :=
  sorry

/-- The structure morphism of the comparison-pullback thickening over `Y` is
formally unramified when `Z ⟶ Y` is. -/
instance comparisonPullbackHom_fst_formallyUnramified [FormallyUnramified i] :
    FormallyUnramified
      (comparisonPullbackHom iZ fZ iY fY i sq ≫
        pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)) :=
  sorry

/-- If `Z ⟶ Y` is formally unramified, the comparison-pullback thickening
`Z ⊂ Y ×_{Y'} Z'` is a universal first-order thickening of `Z` over `Y`. -/
instance comparisonPullback_isUniversal [FormallyUnramified i] :
    IsUniversalFirstOrder (comparisonPullbackHom iZ fZ iY fY i sq)
      (pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
