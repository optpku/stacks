module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.4 is the K-injective null-homotopy theorem, specialized by
the canonical instance on `CochainComplex.InjectivePlus`. -/
@[stacks 013R] #check @CochainComplex.IsKInjective.nonempty_homotopy_zero
@[stacks 013R] #check @CochainComplex.Plus.TermsIn.instIsKInjective

end
