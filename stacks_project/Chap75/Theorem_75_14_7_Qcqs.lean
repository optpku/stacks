/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes.Qcqs

/-!
# Approximation by perfect complexes on qcqs algebraic spaces

Every quasi-compact, quasi-separated algebraic space admits approximation by
perfect complexes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes.of_qcqs :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
      HasApproximationByPerfectComplexes X)
