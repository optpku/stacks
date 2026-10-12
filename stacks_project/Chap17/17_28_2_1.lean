/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
