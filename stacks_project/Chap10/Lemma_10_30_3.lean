module

public import ReasLib.RingTheory.RingHom.Spectrum.Surjective
import StacksCheckRecall

/-!
# Surjectivity criteria for maps on prime spectra

@stack 00FI
-/

@[expose] public section

/- Lemma 10.30.3 (Tag 00FI): the chapter's `algebraMap R S` case is recalled from the
generic ring-hom owner.  The TFAE and its pairwise spectral/ideal/radical bridges are kept
there because those forms are the reusable downstream API. -/
@[stacks 00FI]
#check @PrimeSpectrum.comap_surjective_tfae

/- Pairwise bridges retain the source directions while avoiding `List.TFAE` index arithmetic. -/
@[stacks 00FI]
#check @PrimeSpectrum.prime_contraction_iff_radicalIdeal_contraction
@[stacks 00FI]
#check @PrimeSpectrum.radical_map_comap_iff_prime_contraction

section SourceSpecialization

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- The displayed chapter map is `comap (algebraMap R S)`; this explicit check records the
specialization without creating a duplicate theorem or forcing an `Algebra` assumption on the
generic owner. -/
@[stacks 00FI]
#check PrimeSpectrum.comap_surjective_tfae (algebraMap R S)

end SourceSpecialization

/- The base-change clause is already owned by `Spectrum.BaseChange`; this facade deliberately
does not introduce a chapter-local duplicate. -/
@[stacks 00FI]
#check @PrimeSpectrum.comap_surjective_baseChange

section BaseChangeSpecialization

universe u v w

open scoped TensorProduct

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing R'] [Algebra R R']

/- This explicit check records the source's base-change shape: the generic owner first supplies
surjectivity for `algebraMap R S`, then returns surjectivity for `algebraMap R' (R' ⊗[R] S)`. -/
@[stacks 00FI]
#check PrimeSpectrum.comap_surjective_baseChange (R := R) (S := S) (R' := R')

end BaseChangeSpecialization
