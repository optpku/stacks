module

public import ReasLib.FieldTheory.PrimeField.PowerCriterion.ResidueField
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.3

@stack 0BR8
-/

/-!
# Lemma 10.46.3

The localization and residue-field transport in the textbook proof are instances of the shared
`RingHom.PowerRange.residueField_criterion`.  The chapter entry keeps the source label and the
separate homeomorphism recall, while the reusable map-level predicate lives in ReasLib.
-/

/- Lemma 10.46.3 (1) (Tag 0BR8): the residue-field alternative. -/
@[stacks 0BR8]
#check @RingHom.PowerRange.residueField_criterion

/- Lemma 10.46.3 (2): locally nilpotent kernel gives the spectral homeomorphism. -/
@[stacks 0BR8 "(2)"]
#check @PrimeSpectrum.isHomeomorph_comap

#check @RingHom.IsPowerSurjective
@[stacks 0BR8 "power-surjectivity criterion"]
#check @RingHom.isPowerSurjective_iff_forall_pow_mem_range
