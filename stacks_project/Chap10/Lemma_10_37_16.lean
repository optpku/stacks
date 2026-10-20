module

public import ReasLib.RingTheory.Normal.FiniteProduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.37.16

@stack 030C

For a reduced ring with finitely many minimal primes, the reusable owner
states the source TFAE directly and retains the concrete finite-product
equivalence in its existential clause.
-/

@[stacks 030C "normality, integral closedness, and finite-product decomposition"]
#check @IsNormalRing.tfae_integrallyClosed_finiteProduct
