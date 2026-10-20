/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 42.34.3: intersection with the first Chern class of every pullback of an
invertible module defines a degree-one bivariant Chow class. -/
@[stacks 0B77] #check (@AlgebraicGeometry.ChowCohomology.firstChernClass :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ],
    AlgebraicGeometry.ChowCohomology.degree δ p 1)

#check (@AlgebraicGeometry.ChowCohomology.firstChernClass_apply :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (ℒ : X.Modules) [hℒ : Scheme.Modules.Invertible ℒ]
    {X' : Over S} [LocallyOfFiniteType X'.hom] (f : X' ⟶ Over.mk p)
    (k : ℤ) (α : RelativeChow δ X' k),
    (AlgebraicGeometry.ChowCohomology.firstChernClass δ p ℒ).cap
        f (𝟙 X') f IsPullback.of_id_snd k α =
      @AlgebraicGeometry.ChowGroup.firstChernClassCap S _ δ _ X' _
        ((Scheme.Modules.pullback f.left).obj ℒ)
        (Scheme.Modules.Invertible.pullback f.left hℒ) k α)
