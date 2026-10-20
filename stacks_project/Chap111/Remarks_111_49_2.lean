module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Meromorphic
public import ReasLib.Algebra.Module.Length.Principal
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

/- Remarks 111.49.2 (1): on a Noetherian integral scheme `X`, the meromorphic sheaf `𝒦_X` is
constant with value the function field `K(X)`. The canonical owner is the isomorphism on an
integral scheme. -/
@[stacks 02F5]
#check (AlgebraicGeometry.Scheme.meromorphicFunctionSheaf_isIsomorphic_constantFunctionField :
  ∀ {X : Scheme.{u}} [IsIntegral X],
    IsIsomorphic X.meromorphicFunctionSheaf
      ((constantSheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat).obj
        X.functionField))

/- Remarks 111.49.2 (2): for a Noetherian 1-dimensional local domain `O` and nonzero elements
`a`, `b`, one has `Module.length O (O ⧸ Ideal.span {a * b}) =
Module.length O (O ⧸ Ideal.span {a}) + Module.length O (O ⧸ Ideal.span {b})`. -/
@[stacks 02F5]
#check (Module.length_quotient_span_singleton_mul :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    ringKrullDim R = 1 → ∀ {a b : R}, a ≠ 0 → b ≠ 0 →
      Module.length R (R ⧸ Ideal.span {a * b}) =
        Module.length R (R ⧸ Ideal.span {a}) + Module.length R (R ⧸ Ideal.span {b}))
