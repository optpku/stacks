/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Composition.Fundamental
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 62.14.2: For flat locally finite-type morphisms of relative dimensions
`r` and `e` over a locally Noetherian base, the fundamental relative cycles
compose to the fundamental relative cycle in degree `r + e`. -/
@[stacks 0H6S] #check
  (AlgebraicGeometry.RelativeCycle.comp_closedSubschemeFiberCycleFamily_bot :
    ∀ {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r],
    RelativeCycle.comp (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
          (fiberClosedSubschemeDimensionLE_bot f r))
        (closedSubschemeFiberCycleFamily p (⊥ : Y.IdealSheafData) e
          (fiberClosedSubschemeDimensionLE_bot p e)) =
      closedSubschemeFiberCycleFamily (f ≫ p) (⊥ : X.IdealSheafData) (r + e)
        (fiberClosedSubschemeDimensionLE_bot (f ≫ p) (r + e)))

#check
  (AlgebraicGeometry.RelativeCycle.comp_closedSubschemeFiberCycleFamily_bot_mem_group :
    ∀ {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r],
    RelativeCycle.comp (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
          (fiberClosedSubschemeDimensionLE_bot f r))
        (closedSubschemeFiberCycleFamily p (⊥ : Y.IdealSheafData) e
          (fiberClosedSubschemeDimensionLE_bot p e)) ∈
      RelativeCycle.group (f ≫ p) (r + e))
