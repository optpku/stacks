/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Stratification.Refinement
import StacksCheckRecall

@[expose] public section

/- Lemma 5.28.7: a finite constructible cover admits a subordinate finite constructible
stratification. -/
@[stacks 09Y4]
#check FiniteStratification.exists_constructible_subordinate_to_cover
