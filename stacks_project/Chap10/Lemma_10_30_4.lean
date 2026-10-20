module

public import ReasLib.RingTheory.RingHom.Spectrum.DenseRange
import StacksCheckRecall

/-!
# Dense spectrum maps out of a domain

@stack 00FJ
-/

@[expose] public section

/- Lemma 10.30.4 (Tag 00FJ): for a map out of a domain, injectivity, dense spectral range, and
membership of the generic point in the range are the three clauses of the canonical owner. -/
@[stacks 00FJ]
#check @PrimeSpectrum.denseRange_comap_tfae_of_domain

/- Named pairwise forms avoid `List.TFAE` indexing in downstream proofs. -/
@[stacks 00FJ "dense range and injectivity"]
#check @PrimeSpectrum.denseRange_comap_iff_injective

@[stacks 00FJ "dense range and generic point"]
#check @PrimeSpectrum.denseRange_comap_iff_genericPoint_mem_range
