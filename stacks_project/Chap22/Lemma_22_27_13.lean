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

/- Lemma 22.27.13 (1) (09QU): an admissible cone on the first map of a graded-split short
complex is isomorphic, as a triangle, to its associated triangle. -/
@[stacks 09QU]
#check CompBoundaryAssignment.AdmissibleCone.exists_triangleIso_toShortComplex

/- Lemma 22.27.13 (2) (09QU): the associated triangle of an admissibly monic factorization is
isomorphic to the cone triangle of the original map. -/
@[stacks 09QU]
#check CompBoundaryAssignment.AdmissibleCone.exists_triangleIso_fromFactorization
