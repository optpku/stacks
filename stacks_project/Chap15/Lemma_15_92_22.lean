/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.SpectralSequence.Filtered
import StacksCheckRecall

/-!
# Lemma 15.92.22 (0BKD)

The filtered derived-completion spectral sequence and all of its comparison data are owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.SpectralSequence.Filtered`.

@stack 0BKD
-/

@[expose] public section

/- Lemma 15.92.22 (0BKD): a filtered cochain complex has the canonical derived-completion
spectral sequence for every finitely generated ideal. -/
@[stacks 0BKD]
#check @DerivedCategory.DerivedCompletion.existsFilteredSpectralSequence

#check @DerivedCategory.DerivedCompletion.FilteredSpectralSequence
#check @DerivedCategory.DerivedCompletion.FilteredSpectralSequence.pageOneIso
#check @DerivedCategory.DerivedCompletion.FilteredSpectralSequence.targetIso
#check @DerivedCategory.DerivedCompletion.FilteredSpectralSequence.pageIsDerivedComplete
#check @DerivedCategory.DerivedCompletion.FilteredSpectralSequence.spec
