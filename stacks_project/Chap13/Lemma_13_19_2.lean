module

import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution
import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Existence
import StacksCheckRecall

@[expose] public section

/- Lemma 13.19.2 records the two directions of the bounded-above projective
resolution criterion: a resolution forces eventual positive homology
vanishing, and the generic bounded-above replacement API supplies the converse
construction. -/

@[stacks 0645] #check @CochainComplex.ProjectiveResolution.eventually_isZero_homology
@[stacks 0645] #check @CochainComplex.Minus.TermsIn.exists_quasiIso_of_homology

end
