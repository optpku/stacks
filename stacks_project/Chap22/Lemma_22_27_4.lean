/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Contractible
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.4 (09QK): the cone of an identity morphism is contractible. -/
@[stacks 09QK]
#check CompBoundaryAssignment.AdmissibleCone.id_homotopic_zero

/- The corresponding explicit contracting-homotopy formulation. -/
#check CompBoundaryAssignment.AdmissibleCone.exists_contractingHomotopy
