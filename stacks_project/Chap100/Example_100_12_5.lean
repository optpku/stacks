/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.Quotient

/-!
# Dimension of quotient stacks

The dimension of `[X / G]` for finite-type schemes over a field is
`dim X - dim G`. In particular `dim (BG) = -dim G` may be negative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Example 100.12.5: the dimension of the quotient stack of a finite-type scheme
by a finite-type group scheme over a field is the difference of their dimensions. -/
@[stacks 0AFR] #check (AlgebraicGeometry.AlgebraicStack.dimension_quotient :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k)))
    (X : GroupScheme.Action G) [Algebraic X.X] [Algebraic G.X],
    dimension (quotient G X) =
      dimensionDiff (topologicalKrullDim X.X.left) (topologicalKrullDim G.X.left))

#check (AlgebraicGeometry.AlgebraicStack.dimension_classifying :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) [Algebraic G.X],
    dimension (classifying G) = dimensionDiff 0 (topologicalKrullDim G.X.left))

#check (AlgebraicGeometry.AlgebraicStack.dimension_classifying_lt_zero :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (.of k))) [Algebraic G.X]
    (hG : 0 < topologicalKrullDim G.X.left),
    dimension (classifying G) < (0 : EInt))

end AlgebraicGeometry.AlgebraicStack
