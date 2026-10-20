/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes

/-!
# Approximation by perfect complexes on qcqs algebraic spaces

Every quasi-compact, quasi-separated algebraic space admits approximation by
perfect complexes.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasApproximationByPerfectComplexes

/-- Every quasi-compact, quasi-separated algebraic space admits approximation by
perfect complexes. -/
theorem of_qcqs {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    HasApproximationByPerfectComplexes X := sorry

end HasApproximationByPerfectComplexes

end AlgebraicGeometry.AlgebraicSpace
