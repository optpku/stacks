module

public import ReasLib.RingTheory.Flat.Fiber.Depth
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.1

@stack 0338
-/

/- Lemma 10.163.1 [stacks 0338]: canonical recall of depth additivity for finite
modules along a flat local homomorphism. -/
@[stacks 0338]
#check @Algebra.Fiber.moduleDepth_tensor_eq_add_closed
