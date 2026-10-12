/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Constructible.Local
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.6: constructibility is local on finite retrocompact open
covers. -/
@[stacks 053W]
#check TopologicalSpace.IsOpenCover.isConstructible_iff_preimage_of_finite_retrocompact
