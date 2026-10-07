module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Derived
import StacksCheckRecall

@[expose] public section

/- Lemma 21.31.11 (0D91): the canonical bounded-below composite unit is owned by
`LCCat.SmallToSlice.Derived`; this chapter file only recalls it. -/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace
open scoped CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

namespace LCCat.SmallToSlice

/- Lemma 21.31.11, source tag `0D91`. -/
@[stacks 0D91]
#check @LCCat.SmallToSlice.qcDerivedUnit_isIso

end LCCat.SmallToSlice

end
