module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior algebras of binary direct sums

The exterior algebra of a binary direct sum is the graded tensor product of the two exterior
algebras.  Forgetting the graded multiplication gives an explicit linear equivalence with the
ordinary tensor product.  Both directions are inherited from `CliffordAlgebra.prodEquiv`; in
particular, the inverse is data rather than a choice extracted from bijectivity.
@stack 0FJB
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]

/-- The product of the zero quadratic forms agrees pointwise with the zero quadratic form on the
product module. -/
theorem zeroProd_apply (x : M × N) :
    ((0 : QuadraticForm R M).prod (0 : QuadraticForm R N)) x =
      (0 : QuadraticForm R (M × N)) x := sorry

/-- The identity linear equivalence identifies the zero quadratic form on `M × N` with the
product of the zero quadratic forms on `M` and `N`. -/
@[stacks 0FJB "zero-form direct-sum isometry"]
def zeroProdIsometryEquiv :
    (0 : QuadraticForm R (M × N)).IsometryEquiv
      ((0 : QuadraticForm R M).prod (0 : QuadraticForm R N)) where
  toLinearEquiv := LinearEquiv.refl R (M × N)
  map_app' := zeroProd_apply R M N

/-- The exterior algebra of `M × N` as the graded tensor product of the exterior algebras of
`M` and `N`. -/
@[stacks 0FJB "graded exterior algebra of a direct sum"]
noncomputable def prodGradedEquiv :
    ExteriorAlgebra R (M × N) ≃ₐ[R]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R M) ᵍ⊗[R]
        CliffordAlgebra.evenOdd (0 : QuadraticForm R N)) :=
  (CliffordAlgebra.equivOfIsometry (zeroProdIsometryEquiv R M N)).trans
    (CliffordAlgebra.prodEquiv (0 : QuadraticForm R M) (0 : QuadraticForm R N))

/-- The explicit linear equivalence from the exterior algebra of `M × N` to the ordinary
tensor product of the two exterior algebras.  This is only a linear equivalence because the
ordinary tensor product forgets the Koszul signs in the graded multiplication. -/
@[stacks 0FJB "exterior algebra of a direct sum"]
noncomputable def prodEquiv :
    ExteriorAlgebra R (M × N) ≃ₗ[R]
      ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N :=
  (prodGradedEquiv R M N).toLinearEquiv.trans
    (GradedTensorProduct.of R _ _).symm

/-- A degree-one generator of the exterior algebra of a product decomposes into its two tensor
summands. -/
@[simp, stacks 0FJB "generator under the exterior direct-sum equivalence"]
theorem prodEquiv_apply_ι (m : M) (n : N) :
    prodEquiv R M N (ExteriorAlgebra.ι R (m, n)) =
      ExteriorAlgebra.ι R m ⊗ₜ[R] (1 : ExteriorAlgebra R N) +
        (1 : ExteriorAlgebra R M) ⊗ₜ[R] ExteriorAlgebra.ι R n := sorry

/-- The inverse direct-sum equivalence sends a pure tensor to the wedge product of the two
canonical exterior-algebra inclusions. -/
@[simp, stacks 0FJB "pure tensor under the inverse exterior direct-sum equivalence"]
theorem prodEquiv_symm_apply_tmul
    (x : ExteriorAlgebra R M) (y : ExteriorAlgebra R N) :
    (prodEquiv R M N).symm (x ⊗ₜ[R] y) =
      ExteriorAlgebra.map (LinearMap.inl R M N) x *
        ExteriorAlgebra.map (LinearMap.inr R M N) y := sorry

end ExteriorAlgebra
