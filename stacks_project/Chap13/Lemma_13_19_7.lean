module

import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Lemma 13.19.7 is the bounded-above projective specialization of uniqueness
of K-projective lifts across a quasi-isomorphism. -/
@[stacks 064A] #check @CochainComplex.IsKProjective.homotopic_lifts_of_quasiIso
@[stacks 064A] #check @CochainComplex.ProjectiveMinus.homotopic_lifts_of_quasiIso

end
