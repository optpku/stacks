/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FreeResolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.64.2 (0H7X)

@stack 0H7X
-/

open CategoryTheory

/- Lemma 15.64.2: every filtered cochain complex of modules has a filtered free K-flat
resolution which is a quasi-isomorphism on the underlying complex, every stage, and every
graded piece. -/
@[stacks 0H7X "Lemma 15.64.2"]
#check @FilteredComplex.exists_freeKFlatResolution

/- The canonical underlying-complex map used by the source resolution statement. -/
#check @FilteredComplex.underlyingMap

/- The canonical filtration-stage map used by the source resolution statement. -/
#check @FilteredComplex.stageMap

/- The canonical graded-piece map used by the source resolution statement. -/
#check @FilteredComplex.gradedPieceMap

#check @HomologicalComplex.IsTermwiseFree
#check @HomologicalComplex.IsKFlat
