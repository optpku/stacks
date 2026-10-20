/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Data.Complex.Basic

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

/-- There exists a morphism from the complex affine line to the complex projective line
that is surjective on underlying scheme points. -/
theorem exists_surjective_from_affineLine :
    ∃ f : affineLine ℂ ⟶ scheme ℂ, AlgebraicGeometry.Surjective f := sorry

end AlgebraicGeometry.ProjectiveLine
