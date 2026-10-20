module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
import StacksCheckRecall

/-!
# Chap10 10.70.3 base-change recall

The tensor comparison, its chart map, and the fraction evaluation formulas
are shared ReasLib infrastructure.  This leaf intentionally contains no
second compatibility owner; it remains only as a stable module-level recall
for older import graphs.
-/

@[expose] public section

open scoped AffineBlowupChart TensorProduct

@[stacks 0BIP] #check @AffineBlowupChart.BaseChange.element
#check @AffineBlowupChart.BaseChange.Target
#check @AffineBlowupChart.BaseChange.map
#check @AffineBlowupChart.BaseChange.map_algebraMap
#check @AffineBlowupChart.BaseChange.map_basicFraction
#check @AffineBlowupChart.BaseChange.map_powerFraction
#check @AffineBlowupChart.BaseChange.tensorMap
#check @AffineBlowupChart.BaseChange.tensorMap_tmul
#check @AffineBlowupChart.BaseChange.tensorMap_basicFraction
#check @AffineBlowupChart.BaseChange.tensorMap_powerFraction
#check @AffineBlowupChart.BaseChange.tensorMap_parameter
#check @AffineBlowupChart.BaseChange.tensorMap.surjective
#check @AffineBlowupChart.BaseChange.tensorMap.ker_eq_powerTorsion
#check @AffineBlowupChart.BaseChange.tensorMap.mem_ker_iff
#check @AffineBlowupChart.BaseChange.quotientMap
#check @AffineBlowupChart.BaseChange.quotientMap.equiv

end
