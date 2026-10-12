/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Relations
import StacksCheckRecall

/-!
# Lemma 15.90.5

@stack 05ED
-/

@[expose] public section

/-! # Lemma 15.90.5: relation presentation of a finitely generated ideal -/

/- Lemma 15.90.5, tag `05ED`: the relation module of a finite family maps onto the ideal it
generates, and the generated ideal annihilates the kernel. -/
@[stacks 05ED "relation presentation of a finitely generated ideal"]
#check @KoszulComplex.RelationModule.shortExact

#check @KoszulComplex.RelationModule.span_le_annihilator
