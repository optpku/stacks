/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations

/-!
# Relative dimension under pullback

This module records the fixed relative dimension of the first projection in a
scheme-theoretic pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Fixed relative dimension is preserved by the first projection of a scheme pullback. -/
instance instRelativeDimensionPullbackFstOfRelativeDimension
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) {d : ℕ}
    [RelativeDimension g d] : RelativeDimension (pullback.fst f g) d := sorry

end AlgebraicGeometry.Scheme.Hom
