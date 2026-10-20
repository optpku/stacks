/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A surjective morphism from a smooth curve to a normal curve over a field has smooth target. -/
theorem smooth_of_surjective_of_normal
    {k : Type u} [Field k] {X Y : SchemeOverField k} [Curve X] [Curve Y]
    (f : X ⟶ Y) [Surjective f.left] [Smooth X.hom] (hY : Y.left.isNormal) :
    Smooth Y.hom := sorry

end AlgebraicGeometry.Scheme.Hom
