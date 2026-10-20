/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimit.GlobalSections
import StacksCheckRecall

/-!
# Lemma 7.17.8

The global-sections comparison and its quasi-compact test-set criterion live in ReasLib.
-/

@[expose] public section

/- Lemma 7.17.8 (0GMR) (1): injectivity from monic transitions. -/
@[stacks 0GMR "(1)"] #check @CategoryTheory.GrothendieckTopology.Sheaf.FilteredColimit.GlobalSections.injective_of_transitionMono

/- Lemma 7.17.8 (0GMR) (2): injectivity from a quasi-compact terminal sheaf. -/
@[stacks 0GMR "(2)"] #check @CategoryTheory.GrothendieckTopology.Sheaf.FilteredColimit.GlobalSections.injective_of_quasiCompact

/- Lemma 7.17.8 (0GMR) (3): the isomorphism criterion with monic transitions. -/
@[stacks 0GMR "(3)"] #check @CategoryTheory.GrothendieckTopology.Sheaf.FilteredColimit.GlobalSections.isIso_of_quasiCompact_of_transitionMono

/- Lemma 7.17.8 (0GMR) (4): the quasi-compact test-set criterion. -/
@[stacks 0GMR "(4)"] #check @CategoryTheory.GrothendieckTopology.Sheaf.FilteredColimit.GlobalSections.isIso_of_testSet

#check @CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet
