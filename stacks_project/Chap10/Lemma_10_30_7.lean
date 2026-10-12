/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.MinimalPrime
import StacksCheckRecall

/-!
# Lifting minimal points in the image of a spectrum map

@stack 0CAN
-/

@[expose] public section

/- Lemma 10.30.7 (Tag 0CAN): if a minimal point `p` of `Spec R` lies in the
image of `Spec S → Spec R`, then it is the image of a minimal point of
`Spec S`. The reusable owner hides the ideal-level unpacking. -/
@[stacks 0CAN]
#check @PrimeSpectrum.exists_isMin_comap_eq_of_mem_range
