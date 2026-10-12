/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import ReasLib.Algebra.Category.ModuleCat.PushoutQuotient
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and explicit module pushouts

@stack 0AUM

This file is the tensor-product companion to `ModuleCat.PushoutQuotient`. It describes the kernel
of the right pushout leg after tensoring and packages the resulting injectivity criterion for both
the explicit quotient and the categorical pushout.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat.PushoutQuotient

variable {R : Type u} [CommRing R]
variable {M N P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]
variable {Q : Type w} [AddCommMonoid Q] [Module R Q]

/-- An element is killed by the tensored right leg of the quotient pushout exactly when it comes
from an element killed by the tensored left source map. -/
@[stacks 0AUM "kernel of a tensored quotient-pushout leg"]
theorem mem_ker_inr_rTensor_iff (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (y : TensorProduct R P Q) :
    y ∈ LinearMap.ker ((inr f g).rTensor Q) ↔
      ∃ x : TensorProduct R M Q, (f.rTensor Q) x = 0 ∧ (g.rTensor Q) x = y := sorry

/-- Tensoring the right leg of the quotient pushout is injective exactly when `g` kills every
element killed by `f`. -/
@[stacks 0AUM "injectivity of a tensored quotient-pushout leg"]
theorem injective_inr_rTensor_iff (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    Function.Injective ((inr f g).rTensor Q) ↔
      LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q) := sorry

/-- Categorical form of `mem_ker_inr_rTensor_iff`. -/
@[stacks 0AUM "kernel of a tensored categorical pushout leg"]
theorem mem_ker_pushoutInr_rTensor_iff (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (y : TensorProduct R P Q) :
    y ∈ LinearMap.ker
        (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) ↔
      ∃ x : TensorProduct R M Q, (f.rTensor Q) x = 0 ∧ (g.rTensor Q) x = y := sorry

/-- Tensoring the right leg of a categorical module pushout is injective exactly when `g` kills
every element killed by `f`. -/
@[stacks 0AUM "injectivity of a tensored categorical pushout leg"]
theorem injective_pushoutInr_rTensor_iff (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    Function.Injective
        (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) ↔
      LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q) := sorry

end ModuleCat.PushoutQuotient
