/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange.Pushforward

/-!
# Proper pushforward under flat base change

This file records compatibility of dimension-shifted flat base change with
proper pushforward on Chow groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Dimension-shifted flat base change commutes with proper pushforward on Chow groups. -/
theorem baseChangePullback_map
    {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (delta : S → ℤ) [IsDimensionFunction delta]
    (delta' : S' → ℤ) [IsDimensionFunction delta'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible delta delta' c)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ X) [IsProper f.left] (k : ℤ) :
    (baseChangePullback g delta delta' c hcompat X.hom k).comp
        (map delta Y X f k) =
      (map delta' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
          ((Over.pullback g).map f) (k + c)).comp
        (baseChangePullback g delta delta' c hcompat Y.hom k) := sorry

end AlgebraicGeometry.ChowGroup
