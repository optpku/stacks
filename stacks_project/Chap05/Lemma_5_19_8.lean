/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.Quotient.T0
import StacksCheckRecall

@[expose] public section

/- Lemma 5.19.8: an open quotient of a sober space with the prescribed finite
fiber span relation is Kolmogorov. -/
@[stacks 06NA]
#check @IsOpenQuotientMap.t0Space_of_finiteFibers_of_spanEq
