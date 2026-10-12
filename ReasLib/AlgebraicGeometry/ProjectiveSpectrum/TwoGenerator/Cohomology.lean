/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Cohomology of the two-generator projective spectrum

This module records the positive-degree structure-sheaf cohomology and the
global-sections map of the projective spectrum of a two-generator linear relation.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.TwoGeneratorProj

/-- The structure sheaf of a two-generator projective spectrum has vanishing
cohomology in every positive degree. -/
theorem higherCohomology_isZero (A : CommRingCat.{u}) (f₁ f₂ : A)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Scheme.Modules.cohomology
      (SheafOfModules.unit (ProjectiveScheme A f₁ f₂).ringCatSheaf) p) := sorry

/-- The map on global sections of the canonical morphism from a two-generator
projective spectrum is surjective and has square-zero kernel. -/
instance instAppTopIsSquareZeroExtension (A : CommRingCat.{u}) (f₁ f₂ : A) :
    (toSpec A f₁ f₂).appTop.hom.IsSquareZeroExtension := sorry

end AlgebraicGeometry.TwoGeneratorProj
