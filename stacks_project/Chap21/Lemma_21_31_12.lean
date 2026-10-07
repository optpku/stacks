module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Cohomology
import StacksCheckRecall

@[expose] public section

/- Lemma 21.31.12 (09X4): concrete small/qc cohomology owners live in
`LCCat.SmallToSlice.Cohomology`; this chapter file is a source-label recall facade. -/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace
open scoped CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

namespace LCCat.SmallToSlice

/- Lemma 21.31.12 (1), source tag `09X4`. -/
@[stacks 09X4 "(1), qc cohomology view"]
#check @LCCat.SmallToSlice.qcCohomology

#check @LCCat.SmallToSlice.cohomology_isomorphic_qcPullback

/- Lemma 21.31.12 (2), source tag `09X4`. -/
@[stacks 09X4 "(2), small/qc hypercohomology views"]
#check @LCCat.SmallToSlice.smallHypercohomology
#check @LCCat.SmallToSlice.qcHypercohomology

#check @LCCat.SmallToSlice.hypercohomology_isomorphic_qcPullback

/- Lemma 21.31.12, constant-sheaf example, source tag `09X4`. -/
#check @LCCat.SmallToSlice.constantCohomology_isomorphic_qc
#check @LCCat.SmallToSlice.constantCohomology_isomorphic_qcConstant

end LCCat.SmallToSlice

end
