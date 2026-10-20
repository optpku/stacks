/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Derived
import StacksCheckRecall

@[expose] public section

/- Lemma 21.31.10 (0DCY): the concrete four-clause owners are defined in
`LCCat.SmallToSlice.Derived`; this chapter file is a source-label recall facade. -/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace
open scoped CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

namespace LCCat.SmallToSlice

/- Lemma 21.31.10 (1), source tag `0DCY`. -/
@[stacks 0DCY "(1)"]
#check @LCCat.SmallToSlice.qcPullback_pushforward

@[stacks 0DCY "canonical a_X⁻¹ and its comparison map"]
#check @LCCat.SmallToSlice.aInverseAb
#check @LCCat.SmallToSlice.qcPushforward_aInverse_unit
#check @LCCat.SmallToSlice.qcPushforward_aInverse_unit_isIso
#check @LCCat.SmallToSlice.qcPushforward_aInverse_higherDirectImage_isZero

/- Lemma 21.31.10 (2), source tag `0DCY`. -/
@[stacks 0DCY "(2)"]
#check @LCCat.SmallToSlice.proper_higherDirectImage_qc

/- Lemma 21.31.10 (3), source tag `0DCY`. -/
@[stacks 0DCY "(3)"]
#check @LCCat.SmallToSlice.comparisonDerivedUnit_isIso
#check @LCCat.SmallToSlice.aInverseAbPlus

/- Lemma 21.31.10 (4), source tag `0DCY`. -/
@[stacks 0DCY "(4)"]
#check @LCCat.SmallToSlice.proper_derivedPushforward_qc

end LCCat.SmallToSlice

end
