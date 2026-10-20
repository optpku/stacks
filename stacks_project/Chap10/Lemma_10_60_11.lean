module

public import ReasLib.RingTheory.KrullDimension.Prime.Principal
public import ReasLib.RingTheory.Ideal.Principal.Height
import StacksCheckRecall

/-!
# Principal ideals and height-one prime chains

@stack 00KV

Lemma 10.60.11 is the singleton specialization of the principal-ideal owners
recalled below.
-/

@[expose] public section

@[stacks 00KV "(1), principal-ideal height bound"]
#check @Ideal.IsPrincipal.height_le_one_of_mem_minimalPrimes

@[stacks 00KV "(2), principal-ideal weak cover"]
#check @PrimeSpectrum.wcovBy_of_isPrincipal_of_mem_minimalPrimes_sup
