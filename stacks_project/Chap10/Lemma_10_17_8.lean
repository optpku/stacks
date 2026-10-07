module

import StacksCheckRecall
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Compactness of Prime Spectra Recall

The source theorem is the canonical compact-space instance on `PrimeSpectrum`.

@stack 00E8
-/

universe u

section

variable {R : Type u} [CommSemiring R]

/- Lemma 10.17.8: the Stacks Project states that for a ring `R`, the spectrum `Spec(R)` is
quasi-compact. Mathlib exposes this at the owner level as the canonical instance
`PrimeSpectrum.compactSpace` of `CompactSpace (PrimeSpectrum R)`, already for a commutative
semiring; the textbook ring statement is its special case. -/
@[stacks 00E8 "prime spectra are quasi-compact"]
#check @PrimeSpectrum.compactSpace

end
