module

public import ReasLib.AlgebraicGeometry.AffineSpace.Jacobian
import StacksCheckRecall

/-!
# Jacobian of a polynomial map of affine spaces on relative tangent spaces

The induced map of relative tangent spaces of `𝔸ⁿ_k ⟶ 𝔸ᵐ_k` at a closed point is
multiplication by the Jacobian matrix of the defining polynomials, evaluated at that
point.
-/

@[expose] public section

open CategoryTheory MvPolynomial
open AlgebraicGeometry
open AffineSpace
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Exercise 111.35.11: over an algebraically closed field `k`, a morphism
`homOfPolynomials F : 𝔸(ULift (Fin n); Spec (.of k)) ⟶ 𝔸(ULift (Fin m); Spec (.of k))`
given by polynomials `F` has Jacobian matrix `jacobianMatrix F` with entries
`pderiv i (F j)`. At a closed point `x`, with `y = homOfPolynomials F x`, the induced
map `relativeTangentMapAt (homOfPolynomials F) (𝔸(ULift (Fin m); Spec (.of k)) ↘ Spec (.of k)) x`
of relative tangent spaces is multiplication by
`jacobianMatrixEval F (coordsOfClosedPoint hx)`. -/
@[stacks 029M] #check (AlgebraicGeometry.AffineSpace.tangentMap_eq_jacobian :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (n m : ℕ) (F : Fin m → MvPolynomial (Fin n) k)
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k),
    coordsOfTangent (homOfPolynomials_isClosed_apply F hx)
      (relativeTangentMapAt (homOfPolynomials F)
        (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k)) x
        (homOfPolynomials_residueFieldMap_bijective F hx) (tangentOfCoords_comp F hx v)) =
      (jacobianMatrixEval F (coordsOfClosedPoint hx)).mulVec v)
