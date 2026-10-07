module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction.Injective
public import ReasLib.AlgebraicGeometry.ChowGroup.SplittingPrinciple

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Lemma 42.43.1 (1): a finite family of finite locally free modules admits one projective flat
morphism of fixed relative dimension whose Chow pullback is injective after every base change and
on which every module has an invertible-quotient filtration of its rank. -/
@[stacks 02UL] #check (AlgebraicGeometry.exists_projective_flat_splitting :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
    {ι : Type v} [Finite ι] (E : ι → X.Modules) (r : ι → ℕ)
    [∀ i, Scheme.Modules.IsFiniteLocallyFreeOfRank (r i) (E i)],
    ∃ (P : Scheme.{u}) (π : P ⟶ X) (d : ℕ)
      (h_projective : Projective π) (h_flat : Flat π)
      (h_dimension : Scheme.Hom.RelativeDimension π d),
      @ChowGroup.UniversallyInjectivePullback S X P
          (inferInstance : UniversallyCatenary S) δ
          (inferInstance : IsDimensionFunction δ) p π d h_flat h_dimension ∧
        ∀ i, Scheme.Modules.HasInvertibleQuotientFiltrationOfLength (r i)
          ((Scheme.Modules.pullback π).obj (E i)))

/- Lemma 42.43.1 (2): universal injectivity of Chow pullback for a projective flat morphism
implies injectivity of restriction on Chow cohomology. -/
@[stacks 02UL] #check
  (AlgebraicGeometry.ChowCohomology.restrict_injective_of_universallyInjectivePullback :
  ∀ {S X P : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
    (π : P ⟶ X) (d : ℕ) [Projective π] [Flat π]
    [Scheme.Hom.RelativeDimension π d]
    (hπ : ChowGroup.UniversallyInjectivePullback δ p π d),
    Function.Injective
      (ChowCohomology.restrict δ (Over.homMk π : Over.mk (π ≫ p) ⟶ Over.mk p)))
