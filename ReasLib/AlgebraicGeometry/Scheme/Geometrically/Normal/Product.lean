/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal

/-!
# Products of geometrically normal schemes

This file establishes normality of products over a field when one factor is
geometrically normal and the other is normal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The fiber product over a field of a geometrically normal scheme with a normal scheme is
normal. -/
@[stacks 06DG]
theorem isNormal_pullback_of_geometricallyNormal_left
    (X Y : Over (Spec (CommRingCat.of k)))
    (hX : geometricallyNormal X) (hY : Scheme.isNormal Y.left) :
    Scheme.isNormal (pullback X.hom Y.hom : Scheme) := sorry

end AlgebraicGeometry.SchemeOverField
