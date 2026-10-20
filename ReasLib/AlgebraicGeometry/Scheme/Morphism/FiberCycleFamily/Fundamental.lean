/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme

/-!
# Fundamental fibre-cycle dimension bounds

The identity closed subscheme has the fibre-dimension bound supplied by a
morphism of fixed relative dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The identity closed subscheme `⊥ ⊂ X` has fibrewise dimension at most `r`
when `f : X ⟶ S` has relative dimension `r`. -/
theorem fiberClosedSubschemeDimensionLE_bot {X S : Scheme.{u}} (f : X ⟶ S)
    (r : ℕ) [RelativeDimension f r] :
    f.fiberClosedSubschemeDimensionLE (⊥ : X.IdealSheafData) r := sorry

end AlgebraicGeometry.Scheme.Hom
