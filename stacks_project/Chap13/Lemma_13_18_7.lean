module

import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.7 is the bounded-below injective specialization of uniqueness
of K-injective lifts across a quasi-isomorphism. -/
@[stacks 013S] #check @CochainComplex.IsKInjective.homotopic_lifts_of_quasiIso
@[stacks 013S] #check @CochainComplex.InjectivePlus.homotopic_lifts_of_quasiIso

end
