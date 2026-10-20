/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Henselian.StrictHenselian

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Every stalk ring of an integral normal scheme with separably closed function field is
strictly henselian. -/
theorem strictHenselianLocalRingStalk
    (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    [IsSepClosed X.functionField] (x : X) :
    StrictHenselianLocalRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
