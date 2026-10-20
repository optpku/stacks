/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every stalk of an excellent scheme is an excellent ring. -/
instance instIsExcellentRingStalk {X : Scheme.{u}} [Excellent X] (x : X) :
    IsExcellentRing.{u, u} (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
