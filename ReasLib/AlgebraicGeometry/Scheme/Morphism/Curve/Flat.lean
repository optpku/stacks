/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.Normal

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A dominant morphism between curves over a field is flat when the target is normal. -/
theorem flat_of_isDominant_of_curves
    {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
    [Curve X] [Curve Y] (f : X ⟶ Y) [IsDominant f.left]
    (hY : Y.left.isNormal) :
    Flat f.left := sorry

namespace IsNonconstant

/-- A nonconstant morphism between curves over a field is flat when the target is normal. -/
theorem flat_of_curves
    {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
    [Curve X] [Curve Y] {f : X ⟶ Y} (hf : f.left.IsNonconstant)
    (hY : Y.left.isNormal) :
    Flat f.left := sorry

end IsNonconstant

end AlgebraicGeometry.Scheme.Hom
