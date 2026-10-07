module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.BaseChange.FractionRing
import StacksCheckRecall

/-!
# Associated primes after base change to a fraction ring

@stack 05C1

The canonical localization checks below are the two source clauses.  The same owner also exposes
their formulation for any chosen fraction ring and a combined contraction formula.
-/

@[expose] public section

@[stacks 05C1 "(1), canonical localization form"]
#check @associatedPrimesOfModule.BaseChange.FractionRing.eq_localizedModule

@[stacks 05C1 "(2), canonical contraction form"]
#check @associatedPrimesOfModule.BaseChange.FractionRing.localizedModule_eq_image_comap

@[stacks 05C1 "(1), textbook tensor form"]
#check @associatedPrimesOfModule.BaseChange.FractionRing.eq

@[stacks 05C1 "(2), textbook tensor contraction form"]
#check @associatedPrimesOfModule.BaseChange.FractionRing.baseChange_eq_image_comap

@[stacks 05C1 "combined fraction-ring base-change formula"]
#check @associatedPrimesOfModule.BaseChange.FractionRing.eq_image_comap
