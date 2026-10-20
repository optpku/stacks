/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CompactOpenInduction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes.OpenCover

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes

/-- Every quasi-compact, quasi-separated scheme admits approximation by perfect complexes. -/
theorem of_qcqs (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    HasApproximationByPerfectComplexes X := sorry

end AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes
