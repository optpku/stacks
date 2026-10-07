module

public import ReasLib.RingTheory.Spectrum.Prime.Profinite
import StacksCheckRecall

@[expose] public section

/-!
# Profinite prime spectra

Lemma 10.26.5 (Tag 04MG) uses the canonical spectral and basic-open owners.
@stack 04MG
-/

/- Lemma 10.26.5, tag 04MG: the standard profinite criteria for a prime spectrum. -/
@[stacks 04MG]
#check @PrimeSpectrum.profinite_criteria

@[stacks 04MG "canonical spectral-space criterion"]
#check @SpectralSpace.profinite_criteria

@[stacks 04MG "closed compact opens from principal basic opens"]
#check @PrimeSpectrum.isClosed_compactOpen_of_basicOpen

@[stacks 04MG "minimal-prime generic-point bridge"]
#check @PrimeSpectrum.isGenericPoint_irreducibleComponent_iff_mem_minimalPrimes
