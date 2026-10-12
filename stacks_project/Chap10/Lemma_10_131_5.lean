/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.DirectLimit
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.131.5 [stacks 031G]: canonical recall.  The reusable owner is
`KaehlerDifferential.DirectLimit.comparison_isIso`.  Its directed-order and
two `DirectedSystem` hypotheses express the system data in the source, while
the underlying `comparison` remains available for any compatible preorder
diagram.

@stack 031G
-/
@[stacks 031G]
#check @KaehlerDifferential.DirectLimit.comparison_isIso

#check @KaehlerDifferential.DirectLimit.comparison
#check @KaehlerDifferential.DirectLimit.Stage.baseChange
#check @KaehlerDifferential.DirectLimit.Model.desc
