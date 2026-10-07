module

import ReasLib.Algebra.Homology.CochainComplex.MappingCone.NullHomotopy
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.3

The null-homotopy factorization maps and their specification/compatibility bridges are owned by
the neutral mapping-cone leaf in ReasLib.
-/

namespace CochainComplex

@[stacks 08RI]
#check @MappingConeFactorization.map
@[stacks 08RI]
#check @MappingConeFactorization.inr_comp
@[stacks 08RI]
#check @MappingCoconeFactorization.map
@[stacks 08RI]
#check @MappingCoconeFactorization.comp_fst
@[stacks 08RI]
#check @MappingConeFactorization.exists
@[stacks 08RI]
#check @MappingCoconeFactorization.exists

end CochainComplex
