/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Curve

@[expose] public section

universe u

namespace AlgebraicGeometry.RelativePicard

/-- Over a separably closed field, the relative Picard functor of a smooth projective curve is
representable. -/
@[instance]
theorem functor_isRepresentable_of_smoothProjectiveCurve
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] : (functor X).obj.IsRepresentable := sorry

end AlgebraicGeometry.RelativePicard
