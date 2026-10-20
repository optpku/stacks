/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Iterated
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Tower

/-!
# Push-pull along towers of projective bundles

This module records the Chow-theoretic push-pull formula for a finite tower of
represented projective bundles.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

/-- For a projective-bundle tower `π : P ⟶ X`, there are invertible modules whose
iterated first-Chern cap splits flat pullback by proper pushforward in every Chow degree. -/
theorem existsPushPullFormulaOfTower
    {S X P : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
    (π : P ⟶ X) (T : Scheme.ProjectiveBundle.Tower π) :
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
                T.relativeDimension T.flat T.homRelativeDimension k α)) := sorry

end AlgebraicGeometry.ChowGroup.ProjectiveBundle
