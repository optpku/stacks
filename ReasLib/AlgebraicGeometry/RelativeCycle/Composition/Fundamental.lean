/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Composition
public import ReasLib.AlgebraicGeometry.RelativeCycle.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition.ClosedSubscheme

/-!
# Composition of fundamental relative cycles

Fundamental relative cycles of composable flat morphisms compose to the
fundamental relative cycle of the composite, with relative dimensions added.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

open Scheme.Hom

namespace AlgebraicGeometry.RelativeCycle

/-- For flat morphisms `f : X ⟶ Y` and `p : Y ⟶ S` of relative dimensions
`r` and `e` over a locally Noetherian base, the fundamental fibre-cycle families
compose to the fundamental family of `X / S` in degree `r + e`. -/
@[stacks 0H6S]
theorem comp_closedSubschemeFiberCycleFamily_bot {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r] :
    RelativeCycle.comp (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
          (fiberClosedSubschemeDimensionLE_bot f r))
        (closedSubschemeFiberCycleFamily p (⊥ : Y.IdealSheafData) e
          (fiberClosedSubschemeDimensionLE_bot p e)) =
      closedSubschemeFiberCycleFamily (f ≫ p) (⊥ : X.IdealSheafData) (r + e)
        (fiberClosedSubschemeDimensionLE_bot (f ≫ p) (r + e)) := sorry

/-- At each point of each fibre over a locally Noetherian base, the coefficient
of the composite fundamental families of flat morphisms of relative dimensions
`r` and `e` equals that of the fundamental family of their composite in degree
`r + e`. -/
theorem comp_closedSubschemeFiberCycleFamily_bot_apply {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r]
    (s : S) (x : (f ≫ p).fiber s) :
    CyclesOnFibers.toAlgebraicCycle
        (RelativeCycle.comp
          (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
            (fiberClosedSubschemeDimensionLE_bot f r))
          (closedSubschemeFiberCycleFamily p (⊥ : Y.IdealSheafData) e
            (fiberClosedSubschemeDimensionLE_bot p e))) s x =
      CyclesOnFibers.toAlgebraicCycle
        (closedSubschemeFiberCycleFamily (f ≫ p) (⊥ : X.IdealSheafData) (r + e)
          (fiberClosedSubschemeDimensionLE_bot (f ≫ p) (r + e))) s x := sorry

/-- The composite of fundamental fibre-cycle families of flat morphisms of
relative dimensions `r` and `e` over a locally Noetherian base belongs to the
group `z(X/S, r + e)` of relative cycles. -/
theorem comp_closedSubschemeFiberCycleFamily_bot_mem_group {S X Y : Scheme.{u}}
    (p : Y ⟶ S) (f : X ⟶ Y) (e r : ℕ) [IsLocallyNoetherian S]
    [Flat p] [RelativeDimension p e] [Flat f] [RelativeDimension f r] :
    RelativeCycle.comp (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
          (fiberClosedSubschemeDimensionLE_bot f r))
        (closedSubschemeFiberCycleFamily p (⊥ : Y.IdealSheafData) e
          (fiberClosedSubschemeDimensionLE_bot p e)) ∈
      RelativeCycle.group (f ≫ p) (r + e) := sorry

end AlgebraicGeometry.RelativeCycle
