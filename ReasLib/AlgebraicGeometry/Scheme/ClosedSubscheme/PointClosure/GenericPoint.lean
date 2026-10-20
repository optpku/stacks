/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Integral

/-!
# Generic points of reduced point closures

This file records how the generic point of the reduced closure of a point maps to the
ambient scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

/-- The generic point of the reduced closure of `x` maps to `x`. -/
theorem ι_map_genericPoint {X : Scheme.{u}} (x : X) :
    (ι x).base (genericPoint (scheme x)) = x := sorry

end AlgebraicGeometry.Scheme.PointClosure
