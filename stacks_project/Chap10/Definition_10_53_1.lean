/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Artinian.Characterizations
import StacksCheckRecall

@[expose] public section

/-! @stack 00J5 -/

/- Definition 10.53.1 (Tag 00J5): a commutative ring is Artinian exactly when
its descending chains of ideals stabilize.  The predicate and its ideal-chain
view are owned by `IsArtinianRing` and its reusable characterization theorem. -/
@[stacks 00J5]
#check @IsArtinianRing

@[stacks 00J5]
#check @IsArtinianRing.iff_ideal_antitone_chain_condition

@[stacks 00J5 "descending-chain consequence"]
#check @IsArtinianRing.antitone_chain_condition
