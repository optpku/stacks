module

public import ReasLib.RingTheory.KrullDimension.Prime.Generation
import StacksCheckRecall

/-!
# Height bounds from finitely many generators

@stack 0BBZ

Lemma 10.60.12 is the finite-index specialization of the cardinality bounds
recalled below.
-/

@[expose] public section

@[stacks 0BBZ "(1), canonical height bound"]
#check @Ideal.height_le_card_of_mem_minimalPrimes_span

@[stacks 0BBZ "(2), canonical prime-chain bound"]
#check @PrimeSpectrum.length_le_ncard_of_mem_minimalPrimes_sup_span
