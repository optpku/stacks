/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Reduction

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [PerfectField k]
variable (G : Over (Spec (.of k))) [GrpObj G]

/- Compatibility check for the former group-reduction implementation module. -/
#check (AlgebraicGeometry.Over.reductionClosedSubgroup G :
  AlgebraicGeometry.Scheme.ClosedSubgroup G)
