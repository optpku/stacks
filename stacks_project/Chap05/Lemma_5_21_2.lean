/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.NowhereDense.FiniteUnion
import StacksCheckRecall

@[expose] public section

/- The binary closure property is the reusable companion used by finite unions. -/
#check @IsNowhereDense.union

/- Lemma 5.21.2: a finite union of nowhere dense subsets is nowhere dense. -/
@[stacks 03HO]
#check @IsNowhereDense.sUnion
