/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# Pullback of scheme ideal subobjects

This leaf identifies Mathlib's pullback ideal-sheaf datum with the image
subobject of the pulled-back ideal map on the underlying locally ringed space.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The subobject represented by a pulled-back ideal sheaf is the image of the pulled-back ideal
map to the target structure sheaf. -/
@[simp, stacks 01JU "inverse-image ideal as an image subobject"]
theorem toSubobject_comap
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).toSubobject =
      LocallyRingedSpace.IdealSubobject.pullback I.toSubobject f.toLRSHom := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
