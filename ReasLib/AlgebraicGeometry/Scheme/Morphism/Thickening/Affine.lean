/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.AffineDescent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsThickening

/-- The target of a thickening from an affine scheme is affine. -/
theorem isAffine {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i] [IsAffine X] :
    IsAffine X' := sorry

end AlgebraicGeometry.IsThickening
