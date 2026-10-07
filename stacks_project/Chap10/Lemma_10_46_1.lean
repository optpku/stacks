module

public import ReasLib.RingTheory.RingHom.BaseChange.Surjective
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.1

@stack 0BR6
-/

/-!
# Lemma 10.46.1

The four conclusions for a surjective map with locally nilpotent kernel are already owned by
mathlib and ReasLib.  In particular, the base-change kernel formula is reusable independently of
the spectral application, so the chapter file keeps only source-labelled recall entries.
-/

/- Lemma 10.46.1 (1) (Tag 0BR6): a surjective map with locally nilpotent kernel induces a
homeomorphism on prime spectra. -/
@[stacks 0BR6 "(1)"]
#check @PrimeSpectrum.isHomeomorph_comap

/- Lemma 10.46.1 (2) (Tag 0BR6): a surjective map induces bijections on the corresponding
residue fields. -/
@[stacks 0BR6 "(2)"]
#check @RingHom.SurjectiveOnStalks.residueFieldMap_bijective
#check @RingHom.surjectiveOnStalks_of_surjective

/- Lemma 10.46.1 (3) (Tag 0BR6): surjectivity is preserved by arbitrary tensor-product base
change. -/
@[stacks 0BR6 "(3)"]
#check @RingHom.BaseChange.surjective

/- Lemma 10.46.1 (4) (Tag 0BR6): local nilpotence of the kernel is preserved by arbitrary
tensor-product base change. -/
@[stacks 0BR6 "(4)"]
#check @RingHom.BaseChange.ker_isLocallyNilpotent

/- Fine-grained base-change owners for quotient and ideal arguments. -/
@[stacks 0BR6 "kernel and tensor base-change bridges"]
#check @RingHom.BaseChange.ker_eq_map
@[stacks 0BR6 "left inclusion kernel bridge"]
#check @Algebra.TensorProduct.includeLeft_ker_eq_map
@[stacks 0BR6 "left inclusion locally nilpotent bridge"]
#check @Algebra.TensorProduct.includeLeft_ker_isLocallyNilpotent
