module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
import StacksCheckRecall

@[expose] public section

/- Lemma 13.31.4: in an abelian category, a bounded below cochain complex of injective objects is
K-injective. This is the canonical owner instance on `CochainComplex.InjectivePlus 𝒜`, recalled
here rather than redeclared under a parallel theorem name. -/
@[stacks 070J] #check @CochainComplex.Plus.TermsIn.instIsKInjective
