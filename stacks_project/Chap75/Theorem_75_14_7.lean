/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes.Qcqs
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Theorem 75.14.7: approximation by perfect complexes holds on every quasi-compact,
quasi-separated algebraic space. -/
@[stacks 08HP] #check
  (AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes.of_qcqs :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
      HasApproximationByPerfectComplexes X)
