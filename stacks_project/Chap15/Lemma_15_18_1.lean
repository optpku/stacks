/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Locus.BaseChange
import StacksCheckRecall

/-!
# Base change of the closed-fiber flatness condition

Lemma 15.18.1 is the ideal-of-the-base specialization of the canonical closed-subset base-change
theorem for flatness loci.

@stack 052X
-/

@[stacks 052X "Lemma 15.18.1"]
#check @Ideal.FlatLocus.baseChange

@[stacks 052X "closed-subset flatness locus under base change"]
#check @Ideal.FlatLocus.baseChange_of_map_le
