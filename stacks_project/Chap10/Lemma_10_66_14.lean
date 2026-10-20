module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.14
@stack 05C8

The reusable set owner is `weaklyAssociatedPrimes`; this file keeps only the
source-facing quotient specialization.
-/

-- Lemma 10.66.14: via the canonical map `Spec (R ⧸ I) → Spec R`, the weakly associated primes
-- of the `R ⧸ I`-module `M` map exactly to the weakly associated primes of `M` over `R`.
@[stacks 05C8]
#check @weaklyAssociatedPrimes.image_comap_quotient_eq
