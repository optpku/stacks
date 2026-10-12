/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Characterization
import StacksCheckRecall

open CategoryTheory.MonoidalCategory

universe u

/- Proposition 28.26.13: for a quasi-compact scheme and an invertible module, ampleness is
equivalent to the section-ring, nonvanishing-basis, generation, eventual-global-generation, and
finite-negative-power-quotient conditions. -/
@[stacks 01Q3] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_tfae :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
      [CompactSpace X] [AlgebraicGeometry.Scheme.Modules.Invertible L],
      List.TFAE [
        AlgebraicGeometry.Scheme.Modules.IsAmple L,
        AlgebraicGeometry.Scheme.Modules.IsSectionRingOpenImmersion L,
        TopologicalSpace.Opens.IsBasis
          (AlgebraicGeometry.Scheme.Modules.positiveTensorPowerNonvanishingOpens L),
        TopologicalSpace.Opens.IsBasis
          {U : X.Opens |
            U ∈ AlgebraicGeometry.Scheme.Modules.positiveTensorPowerNonvanishingOpens L ∧
              AlgebraicGeometry.IsAffineOpen U},
        ∀ F : X.Modules, F.IsQuasicoherent →
          AlgebraicGeometry.Scheme.Modules.IsGeneratedByPositivePowers L F,
        ∀ I : CategoryTheory.Subobject (𝟙_ X.Modules),
          (I : X.Modules).IsQuasicoherent →
            AlgebraicGeometry.Scheme.Modules.IsGeneratedByPositivePowers L (I : X.Modules),
        QuasiSeparatedSpace X ∧
          ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
            AlgebraicGeometry.Scheme.Modules.IsEventuallyGloballyGenerated L F,
        QuasiSeparatedSpace X ∧
          ∀ F : X.Modules, F.IsQuasicoherent → F.IsFiniteType →
            AlgebraicGeometry.Scheme.Modules.IsFiniteQuotientOfNegativePower L F,
        QuasiSeparatedSpace X ∧
          ∀ I : CategoryTheory.Subobject (𝟙_ X.Modules),
            (I : X.Modules).IsQuasicoherent → (I : X.Modules).IsFiniteType →
              AlgebraicGeometry.Scheme.Modules.IsFiniteQuotientOfNegativePower
                L (I : X.Modules)])
