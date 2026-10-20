/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.ClosedEmbedding
import StacksCheckRecall

@[expose] public section

/- Lemma 20.20.1 (02UV): for a closed embedding `i : Z ⟶ X` and an abelian sheaf `F` on
`Z`, global cohomology of `F` agrees in every degree with global cohomology of `i_* F`. -/
@[stacks 02UV]
#check @CategoryTheory.Sheaf.ClosedEmbedding.globalComparison_isIso

#check @TopCat.Sheaf.ClosedEmbedding.AddCommGrp.pushforwardExact
#check @CategoryTheory.Sheaf.pushforwardCohomologyMap
#check @CategoryTheory.Sheaf.ClosedEmbedding.comparison_isIso
