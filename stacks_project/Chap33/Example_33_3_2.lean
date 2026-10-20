/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product.Counterexample

@[expose] public section

open CategoryTheory Limits

#check (AlgebraicGeometry.ratSqrtNegOneOverRatVariety :
  AlgebraicGeometry.Variety AlgebraicGeometry.ratSqrtNegOneOverRat)

#check (AlgebraicGeometry.ratSqrtNegOneSelfFiberProductIsoCoprod :
  AlgebraicGeometry.ratSqrtNegOneSelfFiberProduct ≅
    AlgebraicGeometry.ratSqrtNegOneSpec ⨿ AlgebraicGeometry.ratSqrtNegOneSpec)

#check (AlgebraicGeometry.ratSqrtNegOneSelfFiberProductReducible :
  ¬ IrreducibleSpace AlgebraicGeometry.ratSqrtNegOneSelfFiberProduct)

/- Example 33.3.2: for `k = ℚ` and `X = Y = Spec(ℚ(i))`, the product
`X ×[Spec(ℚ)] Y` is not a variety. -/
@[stacks 020G] #check
  (AlgebraicGeometry.ratSqrtNegOneSelfFiberProductOverRatNotVariety :
    ¬ AlgebraicGeometry.Variety AlgebraicGeometry.ratSqrtNegOneSelfFiberProductOverRat)
