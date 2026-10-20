/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes.Qcqs

@[expose] public section

universe u

/- Theorem 36.14.6: approximation by perfect complexes holds on every quasi-compact,
quasi-separated scheme. -/
@[stacks 08ES] #check
  (AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes.of_qcqs :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
      AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes X)
