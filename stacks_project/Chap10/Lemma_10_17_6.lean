/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Spectrum.Prime.Localization.Away

@[expose] public section

/-!
# Spectrum of a Principal Localization Recall

The homeomorphism and its pointwise formulas are owned by `PrimeSpectrum`.

@stack 00E4
-/

/- Lemma 10.17.6: the canonical map `Spec(R_f) → Spec(R)` identifies the spectrum of the
principal localization with the basic open `D(f)`.  The reusable homeomorphism and its point and
inverse-ideal descriptions are owned by `PrimeSpectrum`. -/
@[stacks 00E4 "spectrum of a principal localization"]
#check @PrimeSpectrum.localizationAwayHomeomorph

@[stacks 00E4 "principal-localization spectrum map"]
#check @PrimeSpectrum.localizationAwayHomeomorph_apply

@[stacks 00E4 "inverse ideal under principal localization"]
#check @PrimeSpectrum.localizationAwayHomeomorph_symm_asIdeal
