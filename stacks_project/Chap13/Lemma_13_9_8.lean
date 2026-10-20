module

import ReasLib.Algebra.Homology.CochainComplex.MappingCone.SplitEpiFactorization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.8

The split-epimorphic mapping-cocone factorization is owned by
`ReasLib.Algebra.Homology.CochainComplex.MappingCone.SplitEpiFactorization`.  The chapter entry
keeps the Stacks label while exposing the atomic factorization, retract, computation, and
boundedness APIs.
-/

namespace CochainComplex

@[stacks 0642]
#check @SplitEpiFactorization.obj
@[stacks 0642]
#check @SplitEpiFactorization.desc
@[stacks 0642]
#check @SplitEpiFactorization.projection
@[stacks 0642]
#check @SplitEpiFactorization.section_
@[stacks 0642]
#check @SplitEpiFactorization.coconeMap
@[stacks 0642]
#check @SplitEpiFactorization.map
@[stacks 0642]
#check @SplitEpiFactorization.map_id
@[stacks 0642]
#check @SplitEpiFactorization.map_comp
@[stacks 0642]
#check @SplitEpiFactorization.map_comp_projection
@[stacks 0642]
#check @SplitEpiFactorization.section_comp_map
@[stacks 0642]
#check @SplitEpiFactorization.desc_naturality
@[stacks 0642]
#check @SplitEpiFactorization.homotopyEquiv
@[stacks 0642]
#check @SplitEpiFactorization.desc_f_isSplitEpi
@[stacks 0642]
#check @SplitEpiFactorization.section_comp_desc
@[stacks 0642]
#check @SplitEpiFactorization.section_comp_projection
@[stacks 0642]
#check @SplitEpiFactorization.factorization_spec
@[stacks 0642]
#check @SplitEpiFactorization.cocone_id_plus
@[stacks 0642]
#check @SplitEpiFactorization.cocone_id_bounded_above
@[stacks 0642]
#check @SplitEpiFactorization.plus
@[stacks 0642]
#check @SplitEpiFactorization.bounded_above
@[stacks 0642]
#check @SplitEpiFactorization.bounded

end CochainComplex
