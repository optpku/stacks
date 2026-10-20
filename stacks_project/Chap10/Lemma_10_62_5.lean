module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
import StacksCheckRecall

/-!
# Lemma 10.62.5

@stack 00L7
-/

@[expose] public section

/- Lemma 10.62.5 (1): the minimal factors of a prime filtration are precisely the minimal points
of the module support. -/
@[stacks 00L7 "(1)"]
#check @Module.PrimeFiltration.minimal_primeFactor_iff_minimal_support

/- Lemma 10.62.5 (2): the number of occurrences of a minimal prime factor equals the length of
the localized module at that prime. -/
@[stacks 00L7 "(2)"]
#check @Module.PrimeFiltration.multiplicity_eq_length
