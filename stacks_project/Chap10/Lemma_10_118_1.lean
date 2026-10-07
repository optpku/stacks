module

public import ReasLib.RingTheory.GenericFlatness.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Generic Freeness over a Noetherian Domain

The source-faithful Noetherian bridge is owned by
`GenericFlatness.exists_nonzero_away_module_free`; the stronger finite-type
package remains available as `GenericFlatness.exists_nonzero_away_of_finiteType`.

@stack 051R
-/

/- Lemma 10.118.1: if `R` is Noetherian and a domain, `S` is finite type over
`R`, and `M` is finite over `S`, a nonzero principal localization makes `M`
free over the localized base. -/
@[stacks 051R]
#check @GenericFlatness.exists_nonzero_away_module_free

/- The stronger package also records localized algebra and presentation data. -/
@[stacks 051R "finite-type generic flatness package"]
#check @GenericFlatness.exists_nonzero_away_of_finiteType
