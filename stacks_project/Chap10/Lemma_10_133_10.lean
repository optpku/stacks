module

public import ReasLib.RingTheory.Kaehler.DeRham.DifferentialOperator
import StacksCheckRecall

/-!
# Order of Kahler de Rham differentials

@stack 0G34
-/

@[expose] public section

@[stacks 0G34 "Kahler de Rham differential"]
#check @KaehlerDifferential.DeRham.d_isOrderOne

@[stacks 0G34 "canonical de Rham owner"]
#check @DifferentialOperator.DeRham.isOrderOne
