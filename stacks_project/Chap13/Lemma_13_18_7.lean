/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.7 is the bounded-below injective specialization of uniqueness
of K-injective lifts across a quasi-isomorphism. -/
@[stacks 013S] #check @CochainComplex.IsKInjective.homotopic_lifts_of_quasiIso
@[stacks 013S] #check @CochainComplex.InjectivePlus.homotopic_lifts_of_quasiIso

end
