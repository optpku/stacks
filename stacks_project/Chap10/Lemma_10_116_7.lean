module

public import ReasLib.RingTheory.KrullDimension.FiniteType.FieldExtension
import StacksCheckRecall

@[expose] public section

/-!
# Fiber Dimensions After a Field Extension

@stack 0CWE
-/

/- Lemma 10.116.7 (1): the subtraction-free local-dimension formula. -/
@[stacks 0CWE "(1)"]
#check @Algebra.FiniteType.fiberLocalRingAt_add_krullDim_eq

/- Lemma 10.116.7 (2): the subtraction-free residue-transcendence formula. -/
@[stacks 0CWE "(2)"]
#check @Algebra.FiniteType.fiberLocalRingAt_add_trdeg_eq

/- Lemma 10.116.7 (3): existence of a zero-dimensional fiber-local point. -/
@[stacks 0CWE "(3)"]
#check @Algebra.FiniteType.exists_fiberLocalRingAt_krullDim_eq_zero
