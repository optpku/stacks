/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.FlatLocus
import StacksCheckRecall

/-!
# Flat-locus descent along a directed colimit

Lemma 15.18.3 descends the closed-subset flatness condition for a finitely presented algebra and
module from a directed colimit to one finite stage.

@stack 05LM
-/

@[expose] public section

@[stacks 05LM "Lemma 15.18.3"]
#check @Ring.DirectLimit.FlatLocus.exists_stage
