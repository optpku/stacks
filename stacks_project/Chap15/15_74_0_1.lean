module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
import StacksCheckRecall

/-!
# Derived tensor/internal-Hom adjunction

The fixed-right derived tensor adjunction is owned by `ReasLib` and keeps its ambient tensor
model explicit.  This chapter file records the source equation without rebuilding the adjunction
or installing a chosen closed structure locally.

@stack 0A63
-/

@[expose] public section

/- Equation 15.74.0.1: the fixed-right derived tensor functor is left adjoint to internal Hom. -/
@[stacks 0A63 "derived tensor/internal-Hom adjunction"]
#check @CategoryTheory.DerivedCategory.DerivedTensor.Right.Closed.adjunction

/- The two orientations of the induced Hom equivalence. -/
#check @CategoryTheory.DerivedCategory.DerivedTensor.Right.Closed.homEquiv
#check @CategoryTheory.DerivedCategory.DerivedTensor.Right.Closed.uncurryEquiv
