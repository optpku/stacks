module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.UniversallyInjective
public import ReasLib.AlgebraicGeometry.Scheme.Module.Filtration.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

/-!
# Splitting principle for Chow groups

This module records a projective flat splitting construction for finite
families of finite locally free modules.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A finite family of finite locally free modules admits one projective flat morphism of fixed
relative dimension whose Chow pullback is injective after every base change and on which every
module has an invertible-quotient filtration of its rank. -/
theorem exists_projective_flat_splitting
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
    {ι : Type v} [Finite ι] (E : ι → X.Modules) (r : ι → ℕ)
    [∀ i, Scheme.Modules.IsFiniteLocallyFreeOfRank (r i) (E i)] :
    ∃ (P : Scheme.{u}) (π : P ⟶ X) (d : ℕ)
      (h_projective : Projective π) (h_flat : Flat π)
      (h_dimension : Scheme.Hom.RelativeDimension π d),
      @ChowGroup.UniversallyInjectivePullback S X P
          (inferInstance : UniversallyCatenary S) δ
          (inferInstance : IsDimensionFunction δ) p π d h_flat h_dimension ∧
        ∀ i, Scheme.Modules.HasInvertibleQuotientFiltrationOfLength (r i)
          ((Scheme.Modules.pullback π).obj (E i)) := sorry

end AlgebraicGeometry
