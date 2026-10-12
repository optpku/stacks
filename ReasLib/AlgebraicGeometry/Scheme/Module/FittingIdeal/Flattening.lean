/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Blowup
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.FinitePresentation

/-!
# Flattening by a Fitting-ideal blowup

Blowing up the Fitting ideal of a finitely presented module sheaf that has constant rank on a
scheme-theoretically dense open produces a locally free strict transform. The canonical kernel
of the pullback-to-strict-transform quotient records the remaining finite-presentation,
vanishing, perfectness, and Tor-dimension properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening

/-- The kernel of the canonical quotient from the pullback of a module sheaf to its strict
transform under the blowup of a Fitting ideal. -/
noncomputable abbrev strictTransformKernel
    {X X' : Scheme.{u}} (b : X' ⟶ X) (ℱ : X.Modules) (r : ℕ) :
    (strictTransformAmbient b (𝟙 X)).Modules :=
  kernel (strictTransformπ b ((Scheme.fittingIdealSheaf ℱ r).comap b) (𝟙 X) ℱ)

/-- The blowup of the `r`th Fitting ideal of a finitely presented module sheaf that is finite
locally free of rank `r` on a scheme-theoretically dense open is admissible over that open. -/
theorem isAdmissibleBlowup
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    IsAdmissibleBlowup U b := sorry

/-- The strict transform under the blowup of the `r`th Fitting ideal is finite locally free of
rank `r` when the original finitely presented module sheaf has that rank on a
scheme-theoretically dense open. -/
theorem strictTransform_isFiniteLocallyFreeOfRank
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      (strictTransformModule b ((Scheme.fittingIdealSheaf ℱ r).comap b) (𝟙 X) ℱ) := sorry

/-- The kernel of the pullback-to-strict-transform quotient for the Fitting-ideal blowup is
finitely presented under the scheme-theoretically dense constant-rank hypothesis. -/
theorem kernel_isFinitePresentation
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    (strictTransformKernel b ℱ r).IsFinitePresentation := sorry

/-- The kernel of the pullback-to-strict-transform quotient vanishes over the inverse image of
the scheme-theoretically dense open on which the module sheaf has constant rank. -/
theorem kernel_isZero_over_preimage
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    IsZero ((strictTransformKernel b ℱ r).over ((pullback.fst (𝟙 X) b) ⁻¹ᵁ U)) := sorry

/-- The pullback of a finitely presented module sheaf in the Fitting-ideal flattening
construction is perfect and has Tor dimension at most one. -/
theorem pullback_isPerfect_and_torDimensionLE_one
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    SheafOfModules.IsPerfect ((strictTransformPullbackFunctor b (𝟙 X)).obj ℱ) ∧
      AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE
        ((strictTransformPullbackFunctor b (𝟙 X)).obj ℱ) 1 := sorry

/-- The kernel of the pullback-to-strict-transform quotient in the Fitting-ideal flattening
construction is perfect and has Tor dimension at most one. -/
theorem kernel_isPerfect_and_torDimensionLE_one
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    SheafOfModules.IsPerfect (strictTransformKernel b ℱ r) ∧
      AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE
        (strictTransformKernel b ℱ r) 1 := sorry

end AlgebraicGeometry.Scheme.fittingIdealSheaf.Flattening
