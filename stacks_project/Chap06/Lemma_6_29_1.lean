/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits
import StacksCheckRecall

@[expose] public section

/- Lemma 6.29.1 [009F]: on an opens site, the four section-comparison statements are instances of
the generic filtered-colimit results.  The finite-cover hypothesis is the site-theoretic
predicate `GrothendieckTopology.HasCofinalRefinement`, rather than a second TopCat-specific
encoding by open subsets and `Finset`s. -/
@[stacks 009F "injectivity under injective transition maps"]
recall CategoryTheory.Sites.FilteredColimitSections.injective_of_mono

@[stacks 009F "injectivity over a quasi-compact open"]
recall CategoryTheory.Sites.FilteredColimitSections.injective_of_quasiCompactObject

@[stacks 009F "isomorphism over a quasi-compact open with injective transition maps"]
recall CategoryTheory.Sites.FilteredColimitSections.isIso_of_quasiCompactObject_of_mono

@[stacks 009F "bijectivity from finite covers with quasi-compact overlaps"]
recall CategoryTheory.Sites.FilteredColimitSections.bijective_ofCofinalRefinement

@[stacks 009F "cofinal finite quasi-compact-overlap coverings of an open"]
recall CategoryTheory.GrothendieckTopology.HasCofinalRefinement
