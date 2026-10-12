/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace WeilCohomology

/-- The functional on a Künneth product obtained by transporting the tensor product of
two trace functionals across a bijective Künneth map. -/
noncomputable def tensorProductTrace
    {F : Type u} [Field F] {M : Type v} {N : Type w} {P : Type max v w}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P]
    (kunnethMap : M ⊗[F] N →ₗ[F] P) (h_kunneth : Function.Bijective kunnethMap)
    (traceM : M →ₗ[F] F) (traceN : N →ₗ[F] F) : P →ₗ[F] F :=
  (TensorProduct.lift ((LinearMap.mul F F).compl₁₂ traceM traceN)).comp
    (LinearEquiv.ofBijective kunnethMap h_kunneth).symm.toLinearMap

/-- The tensor-product trace evaluates on an exterior product as the product of traces. -/
theorem tensorProductTrace_kunnethMap_tmul
    {F : Type u} [Field F] {M : Type v} {N : Type w} {P : Type max v w}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P]
    (kunnethMap : M ⊗[F] N →ₗ[F] P) (h_kunneth : Function.Bijective kunnethMap)
    (traceM : M →ₗ[F] F) (traceN : N →ₗ[F] F) (x : M) (y : N) :
    tensorProductTrace kunnethMap h_kunneth traceM traceN (kunnethMap (x ⊗ₜ[F] y)) =
      traceM x * traceN y := sorry

/-- Contract the right tensor factor against a linear functional. -/
noncomputable def contractRight
    {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    (trace : M →ₗ[F] F) : M ⊗[F] M →ₗ[F] M :=
  (TensorProduct.rid F M).toLinearMap.comp (TensorProduct.map LinearMap.id trace)

/-- The canonical interchange of the middle two factors in a fourfold tensor product. -/
noncomputable def tensorInterchange
    (F : Type u) [Field F] (M : Type v) (N : Type w)
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] :
    (M ⊗[F] N) ⊗[F] (M ⊗[F] N) ≃ₗ[F] (M ⊗[F] M) ⊗[F] (N ⊗[F] N) :=
  (TensorProduct.assoc F (M ⊗[F] N) M N).symm ≪≫ₗ
    TensorProduct.congr (TensorProduct.rightComm F M N M) (LinearEquiv.refl F N) ≪≫ₗ
      TensorProduct.assoc F (M ⊗[F] M) N N

end WeilCohomology
