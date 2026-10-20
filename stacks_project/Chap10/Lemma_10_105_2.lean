module

public import ReasLib.RingTheory.Catenary.Basic
import StacksCheckRecall

/-!
# Catenarity of the prime spectrum

@stack 02IH
-/

/- Lemma 10.105.2: a ring `R` is catenary if and only if its prime spectrum is a
catenary topological space. -/
@[stacks 02IH]
#check @isCatenaryRing_iff_catenarySpace_primeSpectrum
