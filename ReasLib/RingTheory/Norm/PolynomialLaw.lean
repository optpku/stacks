module

public import ReasLib.RingTheory.Norm.Projective
public import Mathlib.RingTheory.PolynomialLaw.Basic

/-!
# The polynomial law of a finite-projective algebra norm

After extending scalars, the norm is the projective determinant of multiplication in the
extended algebra. This family supplies the affine polynomial-law data for norms of finite
locally free scheme morphisms.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w

namespace Algebra

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- The finite-projective norm as a polynomial law, computed by the determinant of
multiplication after every extension of scalars. -/
def finiteProjectiveNormPolynomialLaw : B →ₚₗ[A] A where
  toFun' S _ _ x :=
    letI : CommRing S := (algebraMap A S).commSemiringToCommRing
    (Algebra.TensorProduct.rid A S S).symm (finiteProjectiveNorm S x)
  isCompat' := sorry

/-- The value of the norm polynomial law over the ground ring is the finite-projective norm.
-/
theorem finiteProjectiveNormPolynomialLaw_ground (b : B) :
    (finiteProjectiveNormPolynomialLaw A B).ground b = finiteProjectiveNorm A b := sorry

/-- Over any scalar algebra, the norm polynomial law is the norm of the scalar-extended
finite-projective algebra. -/
theorem finiteProjectiveNormPolynomialLaw_toFun
    (S : Type w) [CommRing S] [Algebra A S] (x : S ⊗[A] B) :
    Algebra.TensorProduct.rid A S S ((finiteProjectiveNormPolynomialLaw A B).toFun S x) =
      finiteProjectiveNorm S x := sorry

end Algebra
