module

import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.6

The source-facing filtered-injective resolution and its stronger strict refinement are owned by
`CochainComplex.FilteredInjectivePlus` in ReasLib.
-/

namespace CochainComplex.FilteredInjectivePlus

/- Lemma 13.26.6 (`05TT`): every finite filtered object has a filtered quasi-isomorphism from
its degree-zero complex to a filtered-injective complex which vanishes in negative degrees. -/
@[stacks 05TT] #check
  @exists_quasiIso_single

end CochainComplex.FilteredInjectivePlus
