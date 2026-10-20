module

public import ReasLib.RingTheory.FormalFiber.Serre
import StacksCheckRecall

/-!
# Lemma 15.51.11

@stack 0BIY
-/

@[expose] public section

/- Lemma 15.51.11: Serre's condition `(S_n)` satisfies all five formal-fiber permanence laws. -/
@[stacks 0BIY "Serre S formal-fiber laws"]
#check @FieldAlgebraProperty.serreConditionS.formalFiberLaws

#synth (FieldAlgebraProperty.serreConditionS 1).EssFiniteTypeBaseChange
#synth (FieldAlgebraProperty.serreConditionS 1).IsLocal
#synth (FieldAlgebraProperty.serreConditionS 1).RegularFiberAscent
#synth (FieldAlgebraProperty.serreConditionS 1).FaithfullyFlatDescent
#synth (FieldAlgebraProperty.serreConditionS 1).SeparableExtension
