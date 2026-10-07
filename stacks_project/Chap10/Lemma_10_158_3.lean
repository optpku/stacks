module

public import ReasLib.RingTheory.Kaehler.PthRootDegree
import StacksCheckRecall

/-!
# Purely inseparable root extensions

@stack 07DZ

The source proof uses a successor induction through derivations and intermediate fields.  Those
steps are proof infrastructure; the stable chapter surface is the degree formula for the generated
intermediate field.
-/

@[expose] public section

/- Lemma 10.158.3: independent absolute differentials force the chosen `p`-th roots to contribute
degree `p ^ n`. -/
@[stacks 07DZ]
#check @KaehlerDifferential.Frobenius.relfinrank_adjoin_pthRoots_eq_pow
