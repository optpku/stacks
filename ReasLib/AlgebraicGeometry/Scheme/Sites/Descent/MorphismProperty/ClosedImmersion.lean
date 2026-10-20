/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.Affine

@[expose] public section

universe u

namespace AlgebraicGeometry.IsClosedImmersion

/-- Closed immersions of schemes satisfy effective descent for fpqc coverings. -/
theorem satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.IsClosedImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc := sorry

end AlgebraicGeometry.IsClosedImmersion
