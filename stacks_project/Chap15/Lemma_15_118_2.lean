/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.PicardGroup.Invertible
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.118.2

The reusable TFAE and the dual-identification data are owned by
`ReasLib.RingTheory.PicardGroup.Invertible`; this chapter entry only records the two source
clauses with their Stacks labels.

@stack 0B8I
-/

/- Lemma 15.118.2 (1): finite locally free rank `1`, tensor-invertible, and a tensor-unit witness
are equivalent. -/
@[stacks 0B8I "Lemma 15.118.2 (1): equivalent criteria for an invertible module"]
#check @ModuleCat.Invertible.tfae

/- Lemma 15.118.2 (2): a chosen tensor inverse is isomorphic to `Module.Dual R M`. -/
@[stacks 0B8I "Lemma 15.118.2 (2): a tensor inverse is the dual module"]
#check @Module.Invertible.tensorInverseEquivDual

#check @Module.Invertible.instFiniteLocallyFreeOfRankOne
#check @Module.Invertible.of_finiteLocallyFreeOfRank_one
#check @Module.Invertible.iff_finiteLocallyFreeOfRank_one

end
