module

public import ReasLib.RingTheory.Algebra.IsEpi.ResidueField
import StacksCheckRecall

@[expose] public section

/-!
# Prime spectra and residue fields of algebra epimorphisms

## Canonical recall

Stacks Lemma 10.107.9, tag `04VW`, has two reusable clauses:
`Algebra.IsEpi.specComap_injective` for prime spectra and
`Algebra.IsEpi.ResidueField.mapsBijective` for the family of residue-field
maps. The `@[stacks 04VW "(1)"]` and `@[stacks 04VW "(2)"]` tags are attached
to the canonical owner checks below and to the corresponding ReasLib declarations.

@stack 04VW
-/

@[stacks 04VW "(1)"] #check @Algebra.IsEpi.specComap_injective
@[stacks 04VW "(2)"] #check @Algebra.IsEpi.ResidueField.mapsBijective
#check @RingHom.ResidueField.MapsBijective.map_bijective
