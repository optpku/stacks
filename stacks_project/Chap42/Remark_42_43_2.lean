/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Tower
public import ReasLib.AlgebraicGeometry.ChowGroup.SplittingPrinciple.ProjectiveBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Remark 42.43.2 (1): the splitting morphism can be chosen as an explicit finite tower of
projective bundles of finite locally free modules of positive constant rank. -/
@[stacks 0FVE] #check
  (AlgebraicGeometry.existsProjectiveBundleTowerSplitting :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
      {ι : Type v} [Finite ι] (E : ι → X.Modules) (r : ι → ℕ)
      [∀ i, Scheme.Modules.IsFiniteLocallyFreeOfRank (r i) (E i)],
      ∃ (P : Scheme.{u}) (π : P ⟶ X)
        (T : Scheme.ProjectiveBundle.Tower π),
        @ChowGroup.UniversallyInjectivePullback S X P
            (inferInstance : UniversallyCatenary S) δ
            (inferInstance : IsDimensionFunction δ) p π T.relativeDimension
            T.flat T.homRelativeDimension ∧
          ∀ i, Scheme.Modules.HasInvertibleQuotientFiltrationOfLength (r i)
            ((Scheme.Modules.pullback π).obj (E i)))

/- Remark 42.43.2 (2): for an explicit projective-bundle tower `π : P ⟶ X`, there
are invertible modules whose iterated first-Chern cap splits flat pullback by proper
pushforward in every Chow degree. -/
@[stacks 0FVE] #check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.existsPushPullFormulaOfTower :
    ∀ {S X P : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
      (π : P ⟶ X) (T : Scheme.ProjectiveBundle.Tower π),
      ∃ (L : Fin T.relativeDimension → P.Modules)
        (hL : ∀ i, Scheme.Modules.Invertible (L i)),
        ∀ (k : ℤ)
          (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance k),
          α =
            @ChowGroup.map S (inferInstance : UniversallyCatenary S) δ
              (inferInstance : IsDimensionFunction δ)
              (Over.mk (π ≫ p)) (Over.mk p) (T.locallyOfFiniteTypeComp p)
              (inferInstance : LocallyOfFiniteType p) (Over.homMk π) T.isProper k
              (@ChowGroup.iteratedFirstChernClassCapAt S
                (inferInstance : UniversallyCatenary S) δ
                (inferInstance : IsDimensionFunction δ) (Over.mk (π ≫ p))
                (T.locallyOfFiniteTypeComp p) k T.relativeDimension L hL
              (@ChowGroup.flatPullback S (inferInstance : UniversallyCatenary S) δ
                  (inferInstance : IsDimensionFunction δ)
                  (Over.mk (π ≫ p)) (Over.mk p) (T.locallyOfFiniteTypeComp p)
                  (inferInstance : LocallyOfFiniteType p) (Over.homMk π)
                  T.relativeDimension T.flat T.homRelativeDimension k α)))
