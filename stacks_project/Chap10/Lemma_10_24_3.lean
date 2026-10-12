/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Connected.Idempotent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.24.3

@stack 00EM

A decomposition of an affine prime spectrum into two complementary open subsets is induced by an
idempotent. The corresponding factors are simultaneously complementary principal quotients and
localizations away from the two idempotents.
-/

@[stacks 00EM "complementary open partition"]
#check @PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isCompl_open

/- For the idempotent supplied above, these canonical owners give the product decomposition,
identify both factors as localizations, and identify their spectra with the corresponding basic
opens. Thus the factors are exposed concretely as quotients rather than hidden behind existential
ring types. -/
@[stacks 00EM "complementary quotient product"]
#check @AlgEquiv.prodQuotientOfIsIdempotentElem

@[stacks 00EM "idempotent quotient is an away localization"]
#check @IsLocalization.Away.quotient_of_isIdempotentElem

@[stacks 00EM "spectrum of a quotient"]
#check @Ideal.primeSpectrum_quotient_homeomorph_zeroLocus

@[stacks 00EM "idempotent basic-open identification"]
#check @PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem

@[stacks 00EM "complementary idempotent basic-open identification"]
#check @PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem
