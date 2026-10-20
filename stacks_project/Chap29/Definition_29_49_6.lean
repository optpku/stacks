module

public import Mathlib.AlgebraicGeometry.FunctionField
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 29.49.6: let `X` be an integral scheme. The function field, or the field of rational
functions of `X`, is the canonical owner `X.functionField`, written in the Stacks Project as
`R(X)`. -/
@[stacks 01RW] #check (AlgebraicGeometry.Scheme.functionField :
  (X : Scheme.{u}) → [IrreducibleSpace X] → CommRingCat)

/- For an integral scheme `X`, its function field carries the canonical field structure. -/
#check (AlgebraicGeometry.instFieldCarrierFunctionField :
  (X : Scheme.{u}) → [IsIntegral X] → Field (AlgebraicGeometry.Scheme.functionField X))
