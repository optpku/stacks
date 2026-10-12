/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Integral birational morphisms

This file records the isomorphism criterion for integral birational morphisms
with normal target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsBirational

/-- An integral birational morphism between integral schemes is an isomorphism when its target is
normal. -/
theorem isIso_of_isIntegralHom_of_isNormal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsBirational f] [IsIntegralHom f]
    (hY : Y.isNormal) : IsIso f := sorry

end AlgebraicGeometry.IsBirational
