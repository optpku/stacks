module

public import ReasLib.RingTheory.Spectrum.Prime.Constructible
import StacksCheckRecall

/-!
@stack 0G1P
-/

@[expose] public section

/- Lemma 10.29.3 (Tag 0G1P): a subset of `PrimeSpectrum R` is constructible if
and only if it is a finite union of sets
`PrimeSpectrum.basicOpen f ∩ PrimeSpectrum.zeroLocus (G : Set R)`.

The reusable statement belongs to the canonical prime-spectrum namespace; its
finite-set indexing is the formal counterpart of a finite list of generators. -/
@[stacks 0G1P]
#check @PrimeSpectrum.Constructible.iff_finset_union
