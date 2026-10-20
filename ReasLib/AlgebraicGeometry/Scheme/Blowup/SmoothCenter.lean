/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

/-!
# Smooth blowups along smooth centers

This file records smoothness of a blowup and of its exceptional divisor when both the ambient
scheme and the center are smooth over the same base.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsBlowup

/-- A blowup of a scheme along a center smooth over the same base is smooth over that base. -/
theorem smooth_of_smooth_center {S X X' : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (b : X' ⟶ X) [Smooth f]
    [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] : Smooth (b ≫ f) := sorry

/-- The exceptional divisor of a blowup along a smooth center in a smooth scheme is smooth over
the same base. -/
theorem exceptionalDivisor_smooth_of_smooth_center {S X X' : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (b : X' ⟶ X) [Smooth f]
    [Smooth (I.subschemeι ≫ f)] [IsBlowup b I] :
    Smooth ((I.comap b).subschemeι ≫ b ≫ f) := sorry

end AlgebraicGeometry.IsBlowup
