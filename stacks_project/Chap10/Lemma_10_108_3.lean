module

public import Mathlib.RingTheory.Ideal.Pure
import StacksCheckRecall

@[expose] public section

/-!
# Pure Ideals Are Determined by Their Vanishing Locus

@stack 04PT
-/

universe u

variable {R : Type u} [CommRing R]

/- Lemma 10.108.3 (04PT): pure ideals are determined by their vanishing loci. This is exactly
the canonical theorem `Ideal.zeroLocus_inj_of_pure`. -/
@[stacks 04PT]
#check @Ideal.zeroLocus_inj_of_pure
