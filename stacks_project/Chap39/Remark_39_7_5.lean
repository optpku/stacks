/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RootsOfUnity.ThirdOverRat

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RootsOfUnity

/- Remark 39.7.5 (1): Over `ℚ`, the polynomial `X ^ 3 - 1` factors as the product of
`X - 1` and `X ^ 2 + X + 1`. -/
@[stacks 04L9] #check
  (AlgebraicGeometry.RootsOfUnity.threeRatFactorization :
    (Polynomial.X ^ 3 - 1 : Polynomial ℚ) =
      (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1))

/- Remark 39.7.5 (2): The group scheme `μ₃` over `ℚ` has exactly two irreducible
components. -/
@[stacks 04L9] #check
  (AlgebraicGeometry.RootsOfUnity.threeRatComponentCount :
    Nat.card (irreducibleComponents (μ₃ over (Spec (.of ℚ))).X.left) = 2)

/- Remark 39.7.5 (3): The irreducible component of `μ₃` over `ℚ` that contains the identity
is geometrically irreducible. -/
@[stacks 04L9] #check
  (AlgebraicGeometry.GroupScheme.instGeometricallyIrreducibleIdentityIrreducibleComponent
      (μ₃ over (Spec (.of ℚ))).X :
    GeometricallyIrreducible
      ((μ₃ over (Spec (.of ℚ))).X.left.irreducibleComponentSubschemeι
          (AlgebraicGeometry.GroupScheme.identityIrreducibleComponent
            (μ₃ over (Spec (.of ℚ))).X) ≫
        (μ₃ over (Spec (.of ℚ))).X.hom))

/- Remark 39.7.5 (4): Not every irreducible component of the group scheme `μ₃` over `ℚ`
is geometrically irreducible. -/
@[stacks 04L9] #check
  (AlgebraicGeometry.RootsOfUnity.threeRatNotComponentwiseGeometricallyIrreducible :
    ¬ GeometricallyIrreducible.Components.all (μ₃ over (Spec (.of ℚ))).X.hom)

end AlgebraicGeometry.RootsOfUnity
