module

public import Mathlib.RingTheory.Algebraic.Integral
import StacksCheckRecall

/-!
# Finite and integral field extensions

@stack 00GR

Lemma 10.36.18 follows from the canonical integrality, algebraicity, and
field criteria recalled below.
-/

@[expose] public section

@[stacks 00GR "(1), integral extension field conclusion"]
#check @isField_of_isIntegral_of_isField

@[stacks 00GR "(1), algebraicity conclusion"]
#check @Algebra.IsIntegral.isAlgebraic

@[stacks 00GR "(2), finiteness implies integrality"]
#check @Algebra.IsIntegral.of_finite

@[stacks 00GR "(2), finite algebraicity conclusion"]
#check @Algebra.IsAlgebraic.of_finite
