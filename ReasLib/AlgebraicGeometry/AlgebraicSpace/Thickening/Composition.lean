/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of thickenings of algebraic spaces

If `X ⊂ X'` and `X' ⊂ X''` are thickenings of algebraic spaces over a scheme `S`, then so is
`X ⊂ X''`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A composite of thickenings of algebraic spaces over a scheme is a thickening. -/
instance IsThickening.comp {S : Scheme.{u}} {X X' X'' : AlgebraicSpace S}
    (i : X ⟶ X') (i' : X' ⟶ X'') [IsThickening i] [IsThickening i'] :
    IsThickening (i ≫ i') :=
  sorry

/-- Thickenings of algebraic spaces over `S` are stable under composition as a morphism
property. -/
instance isThickening_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsThickening S : MorphismProperty (AlgebraicSpace S)) where
  comp_mem i i' _ _ := IsThickening.comp i i'

end AlgebraicGeometry.AlgebraicSpace
