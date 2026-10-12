/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.Descent
import StacksCheckRecall

/-!
# Lemma 15.41.7

@stack 07NT
-/

@[expose] public section

/- Lemma 15.41.7: if `g.comp f` is regular and `g` is faithfully flat, then
`f` is regular. -/
@[stacks 07NT] #check @RingHom.Regular.of_comp_of_faithfullyFlat

#check @RingHom.Regular.fiberBaseChange
#check @RingHom.Regular.fiber_baseChange_algEquiv
#check @RingHom.Regular.fiber_baseChange_faithfullyFlat
