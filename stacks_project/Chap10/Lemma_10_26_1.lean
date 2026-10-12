/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.26.1

@stack 00ES
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.26.1 (1): for a prime `𝔭 ⊆ R`, the closure of the singleton `{𝔭}` in `Spec R` is the
closed subset `V(𝔭)`. This is exactly the canonical theorem
`PrimeSpectrum.closure_singleton`. -/
@[stacks 00ES "closure of a point"]
#check @PrimeSpectrum.closure_singleton

/- Lemma 10.26.1 (2): the irreducible closed subsets of `Spec R` are exactly the subsets `V(𝔭)`
for prime ideals `𝔭 ⊆ R`. Canonically, this is the inclusion-reversing order isomorphism
`PrimeSpectrum.pointsEquivIrreducibleCloseds`. -/
@[stacks 00ES "irreducible closed subsets"]
#check @PrimeSpectrum.pointsEquivIrreducibleCloseds

/- Lemma 10.26.1 (3): the irreducible components of `Spec R` are exactly the subsets `V(𝔭)` for
minimal prime ideals `𝔭 ⊆ R`. Canonically, this is the inclusion-reversing order isomorphism
`minimalPrimes.equivIrreducibleComponents`. -/
@[stacks 00ES "irreducible components"]
#check @minimalPrimes.equivIrreducibleComponents
