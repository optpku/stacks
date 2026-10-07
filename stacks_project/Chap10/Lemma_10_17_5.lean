module

public import ReasLib.RingTheory.Spectrum.Prime.Localization.Homeomorph
import StacksCheckRecall

/-!
# Spectrum of a localization

@stack 00E3
-/

@[expose] public section

/- Lemma 10.17.5, tag `00E3`: the source-facing localization-spectrum
homeomorphism is owned by the reusable `PrimeSpectrum` API. -/
@[stacks 00E3]
#check @PrimeSpectrum.localizationHomeomorph

@[stacks 00E3 "forward map"]
#check @PrimeSpectrum.localizationHomeomorph_apply

@[stacks 00E3 "inverse map"]
#check @PrimeSpectrum.localizationHomeomorph_symm_apply

@[stacks 00E3 "inverse ideal"]
#check @PrimeSpectrum.localizationHomeomorph_symm_apply_asIdeal
