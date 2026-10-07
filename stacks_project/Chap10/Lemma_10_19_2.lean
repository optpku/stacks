module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import StacksCheckRecall

/-!
# Surjectivity on spectra and units

@stack 0B7C

Lemma 10.19.2 is the composition of the local-map and unit-map criteria
recalled below.
-/

@[expose] public section

@[stacks 0B7C "local-map criterion"]
#check @IsLocalHom.of_comap_surjective

@[stacks 0B7C "unit-map equivalence"]
#check @isUnit_map_iff
