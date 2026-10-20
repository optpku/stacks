/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.FilteredColimits
import StacksCheckRecall

@[expose] public section

/- Lemma 7.17.7 [0738]: the finite quasi-compact-overlap hypothesis and all four filtered-colimit
section comparisons are neutral site-theoretic statements in
`CategoryTheory.Sites.FilteredColimits`. -/
@[stacks 0738 "quasi-compact pairwise overlaps"] #check @CategoryTheory.GrothendieckTopology.pairwiseOverlaps

@[stacks 0738 "cofinal finite quasi-compact-overlap coverings"] #check @CategoryTheory.GrothendieckTopology.HasCofinalRefinement

@[stacks 0738 "injectivity from monic transition maps"] #check @CategoryTheory.Sites.FilteredColimitSections.injective_of_mono

@[stacks 0738 "injectivity on quasi-compact site objects"] #check @CategoryTheory.Sites.FilteredColimitSections.injective_of_quasiCompactObject

@[stacks 0738 "isomorphism from quasi-compactness and monic transition maps"] #check @CategoryTheory.Sites.FilteredColimitSections.isIso_of_quasiCompactObject_of_mono

@[stacks 0738 "bijectivity from finite quasi-compact-overlap coverings"] #check @CategoryTheory.Sites.FilteredColimitSections.bijective_ofCofinalRefinement
