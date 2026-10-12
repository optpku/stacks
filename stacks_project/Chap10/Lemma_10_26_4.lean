/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Neighborhood.MinimalPrime
import StacksCheckRecall

@[expose] public section

/-!
# Basic-open neighborhoods of minimal primes

@stack 00EV
-/

/- Lemma 10.26.4: the source's quasi-compact open is represented by
`CompactOpens`; membership in `D(f)` and `Disjoint` are its canonical
neighborhood and empty-intersection formulations. -/
@[stacks 00EV]
#check @PrimeSpectrum.exists_basicOpen_disjoint_of_mem_minimalPrimes
