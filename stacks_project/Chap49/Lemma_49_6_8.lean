module

import StacksCheckRecall
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.Locus

@[expose] public section

universe u v

/- Lemma 49.6.8: for a finite type commutative algebra, the zero locus of the Noether
different is the locus of primes where the algebra is not unramified. -/
@[stacks 0BVU] #check (KaehlerDifferential.zeroLocus_noetherDifferent :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B],
    PrimeSpectrum.zeroLocus (KaehlerDifferential.noetherDifferent A B) =
      (Algebra.unramifiedLocus A B)ᶜ)
