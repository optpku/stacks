/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 42.26.4: proper pushforward commutes with intersection by the first Chern class of
the pullback of an invertible module. -/
@[stacks 02SU] #check
  (AlgebraicGeometry.ChowGroup.map_firstChernClassCap :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      (p : X ⟶ Y) [AlgebraicGeometry.IsProper p.left] (k : ℤ)
      (α : AlgebraicGeometry.CycleGroup X.left
        (X.hom.relativeDimensionFunction δ) (k + 1))
      (ℒ : Y.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      AlgebraicGeometry.ChowGroup.map δ X Y p k
          (AlgebraicGeometry.Scheme.Modules.firstChernClassCap X.hom δ
            ((AlgebraicGeometry.Scheme.Modules.pullback p.left).obj ℒ) k α) =
        AlgebraicGeometry.Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
          (AlgebraicGeometry.CycleGroup.mapHom p.left
            (X.hom.relativeDimensionFunction δ)
            (Y.hom.relativeDimensionFunction δ) (k + 1) α))
