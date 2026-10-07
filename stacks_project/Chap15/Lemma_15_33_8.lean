module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski.EtaleBaseChange

/-!
# Lemma 15.33.8

@stack 0D08
-/

@[expose] public section

/- Lemma 15.33.8: the canonical degree `-1` and degree `0` comparison maps
for a compatible square are owned by ReasLib. -/
#check @Algebra.H1Cotangent.presentationBaseChangeComparison
#check @KaehlerDifferential.baseChangeComparison

/- The reusable ind-etale companion statements underlying Lemma 15.33.8. -/
#check @Algebra.H1Cotangent.presentationBaseChangeComparison_bijective_of_indEtale
#check @KaehlerDifferential.baseChangeComparison_bijective_of_indEtale

/- Lemma 15.33.8 (1), tag `0D08`: henselization preserves `H^{-1}` of the
naive cotangent complex under the induced local map. -/
@[stacks 0D08 "(1)"]
#check @Algebra.H1Cotangent.presentationBaseChangeComparison_bijective_of_henselization

/- Lemma 15.33.8 (2), tag `0D08`: henselization preserves `H^0 = Ω` of the
naive cotangent complex under the induced local map. -/
@[stacks 0D08 "(2)"]
#check @KaehlerDifferential.baseChangeComparison_bijective_of_henselization

/- Lemma 15.33.8 (3), tag `0D08`: strict henselization preserves `H^{-1}` of
the naive cotangent complex under the induced local map. -/
@[stacks 0D08 "(3)"]
#check @Algebra.H1Cotangent.presentationBaseChangeComparison_bijective_of_strictHenselization

/- Lemma 15.33.8 (4), tag `0D08`: strict henselization preserves `H^0 = Ω`
of the naive cotangent complex under the induced local map. -/
@[stacks 0D08 "(4)"]
#check @KaehlerDifferential.baseChangeComparison_bijective_of_strictHenselization
