module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCheckRecall

@[expose] public section

/- Equation 17.28.2.1 (08RN): the additive, Leibniz, and base-ring relations presenting relative
Kähler differentials form the canonical relation submodule `KaehlerDifferential.kerTotal`. -/
@[stacks 08RN]
#check @KaehlerDifferential.kerTotal

#check @KaehlerDifferential.kerTotal_eq
#check @KaehlerDifferential.quotKerTotalEquiv
#check @KaehlerDifferential.linearCombination_surjective
