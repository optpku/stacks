/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.LocalizationAwayGapSplit
import StacksCheckRecall

/-!
# Lemma 15.77.4 (068U)

@stack 068U

The residue-field gap-splitting theorem is owned by the pseudo-coherent derived-category leaf.
This Chapter file is its direct official-label recall.
-/

@[expose] public section

/- Lemma 15.77.4 (068U): residue-field homology vanishing gives a principal-local gap splitting
with perfect upper tail. -/
@[stacks 068U "Lemma 15.77.4, localized gap splitting"]
#check @CategoryTheory.exists_localizationAway_gapSplit_of_residueField_homology_isZero

#check @CategoryTheory.exists_localizationAway_split_of_residueField_homology_surjective

#print axioms CategoryTheory.exists_localizationAway_gapSplit_of_residueField_homology_isZero
