module

import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator.Cohomology
import StacksCheckRecall
import stacks_project.Chap38.Example_38_37_11

universe u

/- Lemma 38.38.1 (1): the structure sheaf of the two-generator projective scheme has
vanishing cohomology in every positive degree. -/
@[stacks 0EVJ] #check
  (AlgebraicGeometry.TwoGeneratorProj.higherCohomology_isZero :
    ∀ (A : CommRingCat.{u}) (f₁ f₂ : A) (p : ℕ), 0 < p →
      CategoryTheory.Limits.IsZero
        (AlgebraicGeometry.Scheme.Modules.cohomology
          (SheafOfModules.unit
            (AlgebraicGeometry.TwoGeneratorProj.ProjectiveScheme A f₁ f₂).ringCatSheaf) p))

/- Lemma 38.38.1 (2): the map on global sections induced by the two-generator
projective scheme is surjective and has square-zero kernel. -/
@[stacks 0EVJ] #check
  (AlgebraicGeometry.TwoGeneratorProj.instAppTopIsSquareZeroExtension :
    ∀ (A : CommRingCat.{u}) (f₁ f₂ : A),
      (AlgebraicGeometry.TwoGeneratorProj.toSpec A f₁ f₂).appTop.hom.IsSquareZeroExtension)
