module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Limits
open TopologicalSpace
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace LCCat

/-!
Lemma 21.31.8 is a concrete compatibility statement for the two canonical topologies on `LCCat`.
The generic inverse-image square is already owned by `overMapPullbackComparisonIso`; this file
keeps only the source-facing `LCCat` specializations.  In particular, no arbitrary pair of
topologies or unrelated functors of sites is exposed here.
-/

/- Lemma 21.31.8 (0D92), first square: qc/Zariski relocalization commutes with pullback. -/
@[stacks 0D92 "qc/Zariski square"]
#check @overMapPullbackComparisonIso

/- Lemma 21.31.8 (0D92), second square: the small-topos inverse image commutes with qc
relocalization. -/
@[stacks 0D92 "small/qc square"]
#check @SmallToSlice.qcPullbackIso

/- The source identity `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` is the canonical comparison below. -/
@[stacks 0D92 "description of a_X inverse image"]
#check @SmallToSlice.qcTypePullbackComparisonIso

/- Lemma 21.31.8 (0D92), final assertion: proper direct image comparison. -/
@[stacks 0D92 "direct-image comparison map"]
#check @SmallToSlice.qcPushforwardComparison

/- Lemma 21.31.8 (0D92), final assertion: the canonical map is invertible for proper maps. -/
@[stacks 0D92 "proper direct-image comparison"]
#check @SmallToSlice.qcPushforwardComparison_isIso_of_proper

end LCCat
