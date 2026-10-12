/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.CohenMacaulay
import StacksCheckRecall

/-!
# Lemma 15.51.12

@stack 0BJ9
-/

@[expose] public section

/- Lemma 15.51.12: Cohen-Macaulayness satisfies all five formal-fiber permanence laws. -/
@[stacks 0BJ9 "Cohen-Macaulay formal-fiber laws"]
#check @FieldAlgebraProperty.cohenMacaulay.formalFiberLaws

#synth FieldAlgebraProperty.cohenMacaulay.EssFiniteTypeBaseChange
#synth FieldAlgebraProperty.cohenMacaulay.IsLocal
#synth FieldAlgebraProperty.cohenMacaulay.RegularFiberAscent
#synth FieldAlgebraProperty.cohenMacaulay.FaithfullyFlatDescent
#synth FieldAlgebraProperty.cohenMacaulay.SeparableExtension
