module

public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable.Integral
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.9

The integral, closed-embedding, and residue-field transports have independent
small owners.  Their source-specific conjunction is owned by
`RingHom.ResidueField.MapsPurelyInseparable.isClosedEmbedding_comap_baseChange`.

@stack 0BRC
-/

/- Lemma 10.46.9 (Tag 0BRC): integral maps with injective prime-spectrum maps and purely
inseparable residue fields are closed embeddings, stably under tensor-product base change. -/
@[stacks 0BRC]
#check @RingHom.ResidueField.MapsPurelyInseparable.isClosedEmbedding_comap_baseChange

#check @PrimeSpectrum.isClosedMap_comap_of_isIntegral
#check @RingHom.isIntegral_isStableUnderBaseChange
#check @RingHom.ResidueField.MapsPurelyInseparable.BaseChange.injective_comap
