/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum
import StacksCheckRecall

@[expose] public section

/-!
# Quotient spectra

Compatibility entry point for the source-facing quotient-spectrum comparison.
The reusable owner is `ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum`.

@stack 00E5
-/

/- Lemma 10.17.7: the quotient map identifies `Spec(R ⧸ I)` with the zero
locus of `I` in `Spec(R)`. -/
@[stacks 00E5]
#check @Ideal.primeSpectrum_quotient_homeomorph_zeroLocus

@[stacks 00E5 "forward map"]
#check @Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply

@[stacks 00E5 "inverse ideal"]
#check @Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_symm_asIdeal
