/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FirstChern

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.29.4 (1): pushing the Gysin pullback of a cycle along the zero-scheme
inclusion equals intersection with the first Chern class of the defining invertible module. -/
@[stacks 02T9]
#check (AlgebraicGeometry.Scheme.Modules.map_gysin_eq_firstChernClassCap :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)),
    ChowGroup.map δ (Over.mk (zeroSchemeι ℒ s ≫ p)) (Over.mk p)
        (Over.homMk (zeroSchemeι ℒ s) rfl :
          Over.mk (zeroSchemeι ℒ s ≫ p) ⟶ Over.mk p) k (gysin p δ ℒ s k α) =
      firstChernClassCap p δ ℒ k α)

/- Lemma 42.29.4 (2): effective-Cartier intersection by the zero scheme of `s` agrees
with intersection by the first Chern class of its defining invertible module. -/
@[stacks 02T9]
#check (AlgebraicGeometry.Scheme.Modules.cartierIntersection_eq_firstChernClassCap :
  ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ]
    (s : ℒ.sections) [IsEffectiveCartierDivisor (zeroSchemeι ℒ s)] (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)),
    cartierIntersection p δ ℒ s k α = firstChernClassCap p δ ℒ k α)

end AlgebraicGeometry.Scheme.Modules
