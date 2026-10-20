/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Comparison
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.11 (09QS): twice rotating the triangle of a graded-split short complex gives the
admissible-cone triangle of its connecting morphism. -/
@[stacks 09QS]
#check CompBoundaryAssignment.AdmissibleCone.exists_rotateRotateIso
