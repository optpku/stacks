module

public import ReasLib.RingTheory.KrullDimension.FiniteType.FieldExtension
import StacksCheckRecall

@[expose] public section

/-!
# Local Dimension After Field Extension

@stack 00P4
-/

/- Lemma 10.116.6: local dimension is preserved at corresponding points
after extending the ground field of a finite-type algebra. -/
@[stacks 00P4]
#check @Algebra.FiniteType.topologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
