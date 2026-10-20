/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.SpectralSequence.Cohomology
import StacksCheckRecall

/-!
# Example 15.92.23 (0BKE)

The bounded cohomology spectral sequence for derived completion is owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.SpectralSequence.Cohomology`.

@stack 0BKE
-/

@[expose] public section

/- Example 15.92.23 (0BKE): truncation filtration gives the bounded spectral sequence whose
second page is completed cohomology and whose abutment is cohomology of the completion. -/
@[stacks 0BKE]
#check @DerivedCategory.DerivedCompletion.existsCohomologySpectralSequence

#check @DerivedCategory.DerivedCompletion.CohomologySpectralSequence
#check @DerivedCategory.DerivedCompletion.CohomologySpectralSequence.pageTwoIso
#check @DerivedCategory.DerivedCompletion.CohomologySpectralSequence.targetIso
#check @DerivedCategory.DerivedCompletion.CohomologySpectralSequence.pageIsDerivedComplete
#check @DerivedCategory.DerivedCompletion.CohomologySpectralSequence.spec
