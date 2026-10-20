/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap39.Definition_39_4_3_SubgroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.Reduction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [PerfectField k]
variable (G : Over (Spec (.of k))) [GrpObj G]

/- Lemma 39.7.6: The reduction of a group scheme over a perfect field is a
closed subgroup scheme of `G`. -/
@[stacks 047R] #check (AlgebraicGeometry.Over.reductionClosedSubgroup G :
  AlgebraicGeometry.Scheme.ClosedSubgroup G)
