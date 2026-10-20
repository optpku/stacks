module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
import StacksCheckRecall

/-!
# Chap10 10.70.3 target-surjectivity recall

Surjectivity and kernel membership are properties of the canonical tensor
comparison, not separate chart-specific constructions.  The reusable forms
are exported by `AffineBlowupChart.BaseChange.tensorMap` and its quotient
comparison; this compatibility leaf deliberately has no duplicate proof
chain.
-/

@[expose] public section

open scoped AffineBlowupChart TensorProduct

@[stacks 0BIP] #check @AffineBlowupChart.BaseChange.tensorMap.surjective
#check @AffineBlowupChart.BaseChange.tensorMap.ker_eq_powerTorsion
#check @AffineBlowupChart.BaseChange.tensorMap.mem_ker_iff
#check @AffineBlowupChart.BaseChange.tensorMap.ker_eq_primaryComponent
#check @AffineBlowupChart.BaseChange.quotientMap.bijective
#check @AffineBlowupChart.BaseChange.quotientMap.equiv

end
