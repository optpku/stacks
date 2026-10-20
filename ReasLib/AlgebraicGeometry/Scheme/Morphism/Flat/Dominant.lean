/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Dominance of flat morphisms

This file records the dominance of flat morphisms between integral schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/-- A flat morphism between integral schemes is dominant. -/
instance isDominant_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Flat f] : IsDominant f := sorry

end AlgebraicGeometry.Flat
