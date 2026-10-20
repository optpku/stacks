/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Quotient

/-!
# Dimensions of quotient and classifying stacks

For a finite-type group scheme acting on a finite-type scheme over a field,
the quotient stack has dimension equal to the difference of their dimensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {k : Type u} [Field k]

/-- The dimension of the quotient of a finite-type scheme by a finite-type group
scheme over a field is the difference of their dimensions. -/
theorem dimension_quotient (G : GroupScheme (Spec (.of k))) (X : GroupScheme.Action G)
    [Algebraic X.X] [Algebraic G.X] :
    dimension (quotient G X) =
      dimensionDiff (topologicalKrullDim X.X.left) (topologicalKrullDim G.X.left) :=
  sorry

/-- The dimension of the classifying stack of a finite-type group scheme over a
field is the negative of the dimension of the group scheme. -/
theorem dimension_classifying (G : GroupScheme (Spec (.of k))) [Algebraic G.X] :
    dimension (classifying G) =
      dimensionDiff 0 (topologicalKrullDim G.X.left) :=
  sorry

/-- The classifying stack of a positive-dimensional finite-type group scheme
over a field has strictly negative dimension. -/
theorem dimension_classifying_lt_zero (G : GroupScheme (Spec (.of k)))
    [Algebraic G.X] (hG : 0 < topologicalKrullDim G.X.left) :
    dimension (classifying G) < (0 : EInt) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
