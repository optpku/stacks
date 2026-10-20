/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Admissible.Strictification
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.5 (1) (09QL): an admissibly monic top map permits strictification of the right
map of a homotopy-commutative square. -/
@[stacks 09QL]
#check Comp.IsAdmissibleMono.exists_homotopic_rightMap

/- Lemma 22.27.5 (2) (09QL): an admissibly epic bottom map permits the dual strictification of
the left map. -/
@[stacks 09QL]
#check Comp.IsAdmissibleEpi.exists_homotopic_leftMap

#check Comp.IsAdmissibleMono.exists_rightMap_inK
#check Comp.IsAdmissibleEpi.exists_leftMap_inK
