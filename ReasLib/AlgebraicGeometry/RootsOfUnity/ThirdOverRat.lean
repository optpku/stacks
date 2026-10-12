/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RootsOfUnity.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.IrreducibleComponent

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RootsOfUnity

/-- Over `ℚ`, the polynomial `X ^ 3 - 1` is the product of `X - 1` and
`X ^ 2 + X + 1`. -/
theorem threeRatFactorization :
    (Polynomial.X ^ 3 - 1 : Polynomial ℚ) =
      (Polynomial.X - 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) := sorry

/-- The group scheme `μ₃` over `ℚ` has exactly two irreducible components. -/
theorem threeRatComponentCount :
    Nat.card (irreducibleComponents (μ₃ over (Spec (.of ℚ))).X.left) = 2 := sorry

/-- Not every irreducible component of the group scheme `μ₃` over `ℚ` is geometrically
irreducible. -/
theorem threeRatNotComponentwiseGeometricallyIrreducible :
    ¬ GeometricallyIrreducible.Components.all (μ₃ over (Spec (.of ℚ))).X.hom := sorry

end AlgebraicGeometry.RootsOfUnity
