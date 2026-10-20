/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Affine
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Domain

@[expose] public section

universe u

namespace AlgebraicGeometry.Blowup

/-- The blowup of an integral scheme at a nonzero ideal sheaf is integral. -/
@[stacks 02ND]
theorem isIntegral {X : Scheme.{u}} {I : X.IdealSheafData} (π : Blowup X I)
    [IsIntegral X] (hI : I ≠ 0) : IsIntegral π.scheme := sorry

end AlgebraicGeometry.Blowup
