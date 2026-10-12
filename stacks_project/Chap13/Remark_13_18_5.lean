/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Remark 13.18.5 is the bounded-below specialization of the generic
K-injective quasi-isomorphism transport API. -/
@[stacks 05TF] #check @CochainComplex.IsKInjective.precomp_bijective_of_quasiIso
@[stacks 05TF] #check @CochainComplex.InjectivePlus.precomp_bijective_of_quasiIso

end
