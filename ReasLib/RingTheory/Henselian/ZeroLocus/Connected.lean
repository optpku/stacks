module

public import ReasLib.RingTheory.Henselian.ZeroLocus
public import ReasLib.RingTheory.Spectrum.Prime.Connected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Connected zero loci of henselian pairs

@stack 09Y6

For a henselian pair `(A, I)`, adding `I` to a prime ideal cuts out a connected closed subset of
`PrimeSpectrum A`.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- Lemma 15.11.16 (Stacks `09Y6`): if `(A, I)` is a henselian pair and `p` is a prime of
`A`, then `V(p + I)` is connected. -/
@[stacks 09Y6]
theorem connectedSpace_zeroLocus_prime_add_of_henselianRing
    (I : Ideal A) [HenselianRing A I] (p : PrimeSpectrum A) :
    ConnectedSpace (zeroLocus (((p.asIdeal + I : Ideal A) : Set A))) := sorry

end PrimeSpectrum
