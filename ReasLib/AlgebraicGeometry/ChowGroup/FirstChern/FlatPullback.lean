/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Divisor
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental

/-!
# Flat pullback and first-Chern intersection

This file records the compatibility of flat pullback with first-Chern intersection.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Flat pullback commutes with intersection by the first Chern class of an invertible
module. -/
theorem flatPullback_firstChernClassCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k) :
    @reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance
        ((k - 1) + (r : ℤ)) (k + (r : ℤ) - 1) (CycleGroup.flatDivisorDegree k r)
        (flatPullback δ X Y f r (k - 1)
          (Scheme.Modules.firstChernClassCap Y.hom δ ℒ (k - 1)
            (CycleGroup.reindex (Y.hom.relativeDimensionFunction δ)
              (sub_add_cancel k 1).symm α))) =
      Scheme.Modules.firstChernClassCap X.hom δ
        ((Scheme.Modules.pullback f.left).obj ℒ) (k + (r : ℤ) - 1)
        (CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
          (sub_add_cancel (k + (r : ℤ)) 1).symm
          (CycleGroup.flatPullback δ X Y f r k α)) := sorry

/-- Flat pullback commutes with intersecting the fundamental cycle by the first Chern class
of an invertible module. -/
theorem flatPullback_firstChernClassCap_fundamental
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y) (r : ℕ)
    [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] (k : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k + 1)
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ] :
    flatPullback δ X Y f r k
        (Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
          (@CycleGroup.fundamental Y.left
            (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
            (Y.hom.relativeDimensionFunction δ) (k + 1))) =
      Scheme.Modules.firstChernClassCap X.hom δ
        ((Scheme.Modules.pullback f.left).obj ℒ) (k + (r : ℤ))
        (@CycleGroup.fundamental X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) (k + (r : ℤ) + 1)) := sorry

end AlgebraicGeometry.ChowGroup
