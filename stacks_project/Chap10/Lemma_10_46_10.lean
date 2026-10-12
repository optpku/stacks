/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable.Integral
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.10

The source combines the closed-embedding and surjective-spectrum branches.
The shared owner expresses the resulting homeomorphism and its complete
tensor-product base-change package directly.

@stack 0BRD
-/

/- Lemma 10.46.10 (Tag 0BRD): an integral algebra map with bijective prime-spectrum map and
purely inseparable residue fields is a homeomorphism on spectra, stably under base change. -/
@[stacks 0BRD]
#check @RingHom.ResidueField.MapsPurelyInseparable.isHomeomorph_comap_baseChange

#check @PrimeSpectrum.comap_surjective_baseChange
#check @RingHom.ResidueField.MapsPurelyInseparable.isClosedEmbedding_comap_baseChange
