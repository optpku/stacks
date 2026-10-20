/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Remark 13.19.5 is the bounded-above specialization of the generic
K-projective quasi-isomorphism transport API. -/
@[stacks 0648] #check @CochainComplex.IsKProjective.postcomp_bijective_of_quasiIso
@[stacks 0648] #check @CochainComplex.ProjectiveMinus.postcomp_bijective_of_quasiIso

end
