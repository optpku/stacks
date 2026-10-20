/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over.BaseChange

/-!
# Proper pushforward under flat base change

This file records compatibility of dimension-shifted flat base change with
proper pushforward on cycle groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Dimension-shifted flat base change commutes with proper pushforward on cycle groups. -/
theorem baseChangePullback_map
    {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (delta : S → ℤ) [IsDimensionFunction delta]
    (delta' : S' → ℤ) [IsDimensionFunction delta'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible delta delta' c)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [IsProper f.left] (k : ℤ) :
    (baseChangePullback g delta delta' c hcompat X.hom k).comp
        (mapHom f.left (Y.hom.relativeDimensionFunction delta)
          (X.hom.relativeDimensionFunction delta) k) =
      (mapHom ((Over.pullback g).map f).left
          (((Over.pullback g).obj Y).hom.relativeDimensionFunction delta')
          (((Over.pullback g).obj X).hom.relativeDimensionFunction delta') (k + c)).comp
        (baseChangePullback g delta delta' c hcompat Y.hom k) := sorry

end AlgebraicGeometry.CycleGroup
