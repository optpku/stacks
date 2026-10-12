/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Spectrum.Prime.Irreducible

@[expose] public section

universe u

namespace PrimeSpectrum

/- Exercise 111.6.11: a closed subset `T ⊆ PrimeSpectrum R` is irreducible if and only if
`T = zeroLocus p` for some prime ideal `p ⊆ R`. -/
@[stacks 02D5] #check
  (PrimeSpectrum.isIrreducible_iff_exists_isPrime_zeroLocus :
    ∀ {R : Type u} [CommSemiring R] {T : Set (PrimeSpectrum R)},
      IsClosed T → (IsIrreducible T ↔ ∃ p : Ideal R, p.IsPrime ∧ T = zeroLocus p))

end PrimeSpectrum
