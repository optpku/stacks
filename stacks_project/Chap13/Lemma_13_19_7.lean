/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Lemma 13.19.7 is the bounded-above projective specialization of uniqueness
of K-projective lifts across a quasi-isomorphism. -/
@[stacks 064A] #check @CochainComplex.IsKProjective.homotopic_lifts_of_quasiIso
@[stacks 064A] #check @CochainComplex.ProjectiveMinus.homotopic_lifts_of_quasiIso

end
