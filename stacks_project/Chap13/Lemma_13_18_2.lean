/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Existence
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.2 records the two directions of the bounded-below injective
resolution criterion: a resolution forces eventual negative homology
vanishing, and the generic bounded-below replacement API supplies the converse
construction. -/

@[stacks 013J] #check @CochainComplex.InjectiveResolution.eventually_isZero_homology
@[stacks 013J] #check @CochainComplex.Plus.TermsIn.exists_quasiIso_of_homology

end
