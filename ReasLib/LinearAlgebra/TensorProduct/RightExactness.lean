/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Tactic.CrossRefAttribute

/-!
# A tensor right-exactness criterion for bijectivity

This leaf packages the elementary consequence of tensor right exactness used
when the left map of an exact pair vanishes after tensoring.
-/

@[expose] public section

universe u v w x y

namespace TensorProduct.RightExact

variable {R : Type u} [CommRing R]
variable {Q : Type v} [AddCommGroup Q] [Module R Q]
variable {M : Type w} {N : Type x} {P : Type y}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

/-- If `f, g` are exact, `g` is surjective, and tensoring `f` with `Q`
vanishes, then tensoring `g` with `Q` is bijective. -/
@[stacks 02HQ "tensor right-exactness bijectivity criterion"]
theorem lTensor_bijective {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hzero : LinearMap.lTensor Q f = 0) :
    Function.Bijective (LinearMap.lTensor Q g) := sorry

end TensorProduct.RightExact
