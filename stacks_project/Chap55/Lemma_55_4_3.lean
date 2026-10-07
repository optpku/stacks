module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionCokernel

/- Lemma 55.4.3 -/
@[stacks 0CE7] #check (NumericalType.picardToIntersectionCokernel_injective :
  ∀ (T : NumericalType), Function.Injective T.picardToIntersectionCokernel)
