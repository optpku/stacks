/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.4 is the K-injective null-homotopy theorem, specialized by
the canonical instance on `CochainComplex.InjectivePlus`. -/
@[stacks 013R] #check @CochainComplex.IsKInjective.nonempty_homotopy_zero
@[stacks 013R] #check @CochainComplex.Plus.TermsIn.instIsKInjective

end
