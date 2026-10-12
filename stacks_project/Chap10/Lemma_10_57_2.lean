/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.DegreeZero.Spectrum
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.57.2

Homogeneous prime ideals in a `ℤ`-graded ring with a positive-degree homogeneous unit are
identified with the prime spectrum of its degree-zero part.

@stack 00JO
-/

/- Lemma 10.57.2 (Tag 00JO): if a `ℤ`-graded ring contains an invertible homogeneous
element of positive degree, contraction to the degree-zero part is a homeomorphism from the
subspace of homogeneous prime ideals onto `Spec(S₀)`. -/
@[stacks 00JO]
#check @PrimeSpectrum.isHomeomorph_comap_degreeZero
