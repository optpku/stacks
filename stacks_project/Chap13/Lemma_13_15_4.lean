/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement
import StacksCheckRecall

@[expose] public section

/- Lemma 13.15.4 is the property-neutral bounded-above replacement API.  The
source item records the two canonical existence statements; construction data
belongs to the reusable cochain-complex owner. -/

@[stacks 05T7] #check @CochainComplex.Minus.TermsIn.exists_epiQuasiIso_of_bound
@[stacks 05T7] #check @CochainComplex.Minus.TermsIn.exists_quasiIso_of_homology
@[stacks 05T7] #check @CochainComplex.Minus.TermsIn.Resolution.nonempty_epi_of_bound
@[stacks 05T7] #check @CochainComplex.Minus.TermsIn.Resolution.nonempty_of_homology

end
