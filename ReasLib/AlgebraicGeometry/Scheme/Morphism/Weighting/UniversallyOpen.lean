/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.BaseChange

/-!
# Universal openness from positive weightings

This module relates positive integer-valued weightings of locally quasi-finite
scheme morphisms to universal openness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type, locally quasi-finite scheme morphism with an everywhere
strictly positive integer-valued weighting is universally open. -/
theorem IsWeighting.universallyOpen {X Y : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {w : X → ℤ}
    (hw : f.IsWeighting w) (h_pos : ∀ x : X, 0 < w x) : UniversallyOpen f := sorry

end AlgebraicGeometry.Scheme.Hom
