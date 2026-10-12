/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Ideal.PrimeAvoidance

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Two points outside the zero locus of an ideal lie in a common basic open defined by an element of that ideal. -/
theorem exists_basicOpen_pair {A : Type u} [CommRing A] (I : Ideal A) (x1 x2 : PrimeSpectrum A)
    (hx1 : x1 ∉ zeroLocus (I : Set A)) (hx2 : x2 ∉ zeroLocus (I : Set A)) :
    ∃ f ∈ I, x1 ∈ basicOpen f ∧ x2 ∈ basicOpen f := sorry

end PrimeSpectrum
