module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization
public import ReasLib.RingTheory.ReesAlgebra.Grading.Structure
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Transport
import StacksCheckRecall

/-!
# Chap10 10.70.3 localization recall

The former version of this support leaf rebuilt the Rees grading, degree-zero
coefficients, and the chart-to-localization comparison locally.  Those are
library constructions now.  This module is kept as a stable import path while
downstream code moves to the canonical ReasLib owners below.
-/

@[expose] public section

open scoped AffineBlowupChart TensorProduct

@[stacks 0BIP] #check @ReesAlgebra.Grading.gradedMap
#check @ReesAlgebra.Grading.gradedMap_degreeOne
#check @ReesAlgebra.Grading.zeroAlgebraMap
#check @HomogeneousLocalization.Transport.awayMap_fromZeroRingHom
#check @AffineBlowupChart.toLocalizationAway
#check @AffineBlowupChart.toLocalizationAway_injective
#check @AffineBlowupChart.toLocalizationAway_basicFraction
#check @AffineBlowupChart.toLocalizationAway_powerFraction
#check @AffineBlowupChart.basicFraction_mul_parameter
#check @AffineBlowupChart.powerFraction_mul_parameter
#check @AffineBlowupChart.BaseChange.map
#check @AffineBlowupChart.BaseChange.tensorMap
#check @AffineBlowupChart.BaseChange.tensorMap_tmul

end
