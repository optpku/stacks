module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.FinitePresentation
import StacksCheckRecall

/-!
# Critere de platitude par fibres

@stack 00R7

The chapter entry checks the reusable approximation-stable criterion directly.
The canonical closed fiber is `Ideal.Fiber`; no chapter-local notation or
instance selection remains.
-/

@[expose] public section

@[stacks 00R7 "module clause"]
#check @Module.Flat.ClosedFiber.of_essFinitePresentation

@[stacks 00R7 "ring-map clause"]
#check @RingHom.Flat.ClosedFiber.of_essFinitePresentation
