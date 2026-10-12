/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.UniversallyInjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

/-!
# Injectivity of restriction on Chow cohomology

This module relates universal injectivity of Chow pullback to injectivity of
the induced restriction map on Chow cohomology.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChowCohomology

/-- Universal injectivity of Chow pullback for a projective flat morphism implies injectivity of
restriction on Chow cohomology. -/
theorem restrict_injective_of_universallyInjectivePullback
    {S X P : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
    (π : P ⟶ X) (d : ℕ) [Projective π] [Flat π]
    [Scheme.Hom.RelativeDimension π d]
    (hπ : ChowGroup.UniversallyInjectivePullback δ p π d) :
    Function.Injective
      (restrict δ (Over.homMk π : Over.mk (π ≫ p) ⟶ Over.mk p)) := sorry

end AlgebraicGeometry.ChowCohomology
