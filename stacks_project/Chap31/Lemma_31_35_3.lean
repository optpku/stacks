module

import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Flattening
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 31.35.3 (1): the blowup in the `r`th Fitting ideal is admissible over the
scheme-theoretically dense open on which the finitely presented module has rank `r`. -/
@[stacks 0ESN]
#check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.isAdmissibleBlowup :
    ∀ {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
      [ℱ.IsFinitePresentation] (r : ℕ)
      (_ : schemeTheoreticallyDense U)
      (_ : SheafOfModules.IsFiniteLocallyFreeOfRank r
        ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
      [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)],
      IsAdmissibleBlowup U b)

/- Lemma 31.35.3 (2): the strict transform under the Fitting-ideal blowup is finite locally
free of rank `r`. -/
@[stacks 0ESN]
#check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.strictTransform_isFiniteLocallyFreeOfRank :
    ∀ {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
      [ℱ.IsFinitePresentation] (r : ℕ)
      (_ : schemeTheoreticallyDense U)
      (_ : SheafOfModules.IsFiniteLocallyFreeOfRank r
        ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
      [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)],
      SheafOfModules.IsFiniteLocallyFreeOfRank r
        (strictTransformModule b ((Scheme.fittingIdealSheaf ℱ r).comap b) (𝟙 X) ℱ))

/- Lemma 31.35.3 (3): the kernel of the canonical pullback-to-strict-transform quotient is
finitely presented. -/
@[stacks 0ESN]
#check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.kernel_isFinitePresentation :
    ∀ {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
      [ℱ.IsFinitePresentation] (r : ℕ)
      (_ : schemeTheoreticallyDense U)
      (_ : SheafOfModules.IsFiniteLocallyFreeOfRank r
        ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
      [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)],
      (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.strictTransformKernel b ℱ r).IsFinitePresentation)

/- Lemma 31.35.3 (4): the strict-transform kernel vanishes after restriction to the inverse
image of the dense open. -/
@[stacks 0ESN]
#check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.kernel_isZero_over_preimage :
    ∀ {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
      [ℱ.IsFinitePresentation] (r : ℕ)
      (_ : schemeTheoreticallyDense U)
      (_ : SheafOfModules.IsFiniteLocallyFreeOfRank r
        ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
      [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)],
      IsZero ((AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.strictTransformKernel b ℱ r).over
        ((pullback.fst (𝟙 X) b) ⁻¹ᵁ U)))

/- Lemma 31.35.3 (5): the pullback module is perfect and has Tor dimension at most one. -/
@[stacks 0ESN]
#check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.pullback_isPerfect_and_torDimensionLE_one :
    ∀ {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
      [DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules (strictTransformAmbient b (𝟙 X)).toRingedSpace)]
      [ℱ.IsFinitePresentation] (r : ℕ)
      (_ : schemeTheoreticallyDense U)
      (_ : SheafOfModules.IsFiniteLocallyFreeOfRank r
        ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
      [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)],
      SheafOfModules.IsPerfect ((strictTransformPullbackFunctor b (𝟙 X)).obj ℱ) ∧
        AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE
          ((strictTransformPullbackFunctor b (𝟙 X)).obj ℱ) 1)

/- Lemma 31.35.3 (6): the strict-transform kernel is perfect and has Tor dimension at most
one. -/
@[stacks 0ESN]
#check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.kernel_isPerfect_and_torDimensionLE_one :
    ∀ {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
      [DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules (strictTransformAmbient b (𝟙 X)).toRingedSpace)]
      [ℱ.IsFinitePresentation] (r : ℕ)
      (_ : schemeTheoreticallyDense U)
      (_ : SheafOfModules.IsFiniteLocallyFreeOfRank r
        ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
      [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)],
      SheafOfModules.IsPerfect
          (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.strictTransformKernel b ℱ r) ∧
        AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE
          (AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening.strictTransformKernel b ℱ r) 1)
