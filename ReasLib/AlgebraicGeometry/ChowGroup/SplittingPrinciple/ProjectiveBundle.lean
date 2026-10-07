module

public import ReasLib.AlgebraicGeometry.ChowGroup.SplittingPrinciple
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Tower

/-!
# Projective-bundle form of the splitting principle

This module refines the splitting construction for finite families of finite
locally free modules by recording an explicit tower of projective bundles.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A finite family of finite locally free modules admits a splitting morphism that is an
explicit finite tower of projective bundles of positive finite constant rank. -/
theorem existsProjectiveBundleTowerSplitting
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
    {ι : Type v} [Finite ι] (E : ι → X.Modules) (r : ι → ℕ)
    [∀ i, Scheme.Modules.IsFiniteLocallyFreeOfRank (r i) (E i)] :
    ∃ (P : Scheme.{u}) (π : P ⟶ X)
      (T : Scheme.ProjectiveBundle.Tower π),
      @ChowGroup.UniversallyInjectivePullback S X P
          (inferInstance : UniversallyCatenary S) δ
          (inferInstance : IsDimensionFunction δ) p π T.relativeDimension
          T.flat T.homRelativeDimension ∧
        ∀ i, Scheme.Modules.HasInvertibleQuotientFiltrationOfLength (r i)
          ((Scheme.Modules.pullback π).obj (E i)) := sorry

end AlgebraicGeometry
