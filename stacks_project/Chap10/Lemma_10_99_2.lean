module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.RegularElement
import StacksCheckRecall

/-!
# Lifting a Nonzerodivisor from the Closed Fiber

@stack 00MF
-/

@[expose] public section

@[stacks 00MF "closed-fiber multiplication is injective"]
#check @LinearMap.ClosedFiber.mul_quotientMap_injective

@[stacks 00MF "(1), flat principal quotient"]
#check @RingHom.Flat.ClosedFiber.flat_quotient_span_singleton

@[stacks 00MF "(2), lifted regular element"]
#check @RingHom.Flat.ClosedFiber.isRegular

@[stacks 00MF "combined source form"]
#check @RingHom.Flat.ClosedFiber.flat_quotient_span_singleton_and_isRegular
