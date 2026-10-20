module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Lifting
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.18.6

The bounded-below injective lifting statements are owned by the neutral
`CochainComplex.InjectivePlus` API.  This chapter file preserves the source labels and exposes
only the canonical recall surface.
-/

/- Lemma 13.18.6 (1): homotopy lifting into a bounded-below injective complex. -/
@[stacks 013P]
#check @CochainComplex.InjectivePlus.exists_homotopy_lift

/- Lemma 13.18.6 (2): strict lifting when the comparison is termwise monomorphic. -/
@[stacks 013P]
#check @CochainComplex.InjectivePlus.exists_lift_of_termwiseMono
