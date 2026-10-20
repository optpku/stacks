module

import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
import StacksCheckRecall

@[expose] public section

/- Lemma 13.15.5 is the property-neutral bounded-below replacement API.  The
source item records the two canonical existence statements; construction data
belongs to the reusable cochain-complex owner. -/

@[stacks 05T6] #check @CochainComplex.Plus.TermsIn.exists_monoQuasiIso_of_bound
@[stacks 05T6] #check @CochainComplex.Plus.TermsIn.exists_quasiIso_of_homology
@[stacks 05T6] #check @CochainComplex.Plus.TermsIn.Resolution.nonempty_mono_of_bound
@[stacks 05T6] #check @CochainComplex.Plus.TermsIn.Resolution.nonempty_of_homology

end
