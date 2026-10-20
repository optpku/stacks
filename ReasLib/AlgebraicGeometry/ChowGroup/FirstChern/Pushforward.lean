/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.WeilDivisor.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental.Pushforward

/-!
# Proper pushforward and first-Chern intersection

This file establishes compatibility of proper pushforward with first-Chern intersection,
including function-field-degree formulas for fundamental cycles.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Proper pushforward of first-Chern intersection with the fundamental cycle equals the
function-field-degree multiple of the corresponding intersection on the target. -/
theorem map_firstChernClassCap_fundamental
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (k : ℤ) (f : X ⟶ Y)
    [IsProper f.left] [IsDominant f.left]
    (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = k + 1)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k + 1)
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ] :
    map δ X Y f k
        (Scheme.Modules.firstChernClassCap X.hom δ
          ((Scheme.Modules.pullback f.left).obj ℒ) k
          (@CycleGroup.fundamental X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) (k + 1))) =
      (f.left.inducedFunctionFieldDegree : ℤ) •
        Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
          (@CycleGroup.fundamental Y.left
            (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
            (Y.hom.relativeDimensionFunction δ) (k + 1)) := sorry

/-- The function-field-degree multiple of first-Chern intersection on the target is first-Chern
intersection with the proper pushforward of the source fundamental cycle. -/
theorem firstChernClassCap_map_fundamental
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (k : ℤ) (f : X ⟶ Y)
    [IsProper f.left] [IsDominant f.left]
    (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = k + 1)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k + 1)
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ] :
    (f.left.inducedFunctionFieldDegree : ℤ) •
        Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
          (@CycleGroup.fundamental Y.left
            (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
            (Y.hom.relativeDimensionFunction δ) (k + 1)) =
      Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
        (CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) (k + 1)
          (@CycleGroup.fundamental X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) (k + 1))) := sorry

/-- Proper pushforward commutes with first-Chern intersection by an invertible module on the
target. -/
theorem map_firstChernClassCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) [IsProper p.left] (k : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k + 1))
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ] :
    map δ X Y p k
        (Scheme.Modules.firstChernClassCap X.hom δ
          ((Scheme.Modules.pullback p.left).obj ℒ) k α) =
      Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
        (CycleGroup.mapHom p.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) (k + 1) α) := sorry

end AlgebraicGeometry.ChowGroup
