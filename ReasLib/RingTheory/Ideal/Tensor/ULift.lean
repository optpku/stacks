/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Tensor

/-!
# Universe Lifts of Ideal Tensor Multiplication

This leaf records the universe-polymorphic transport of injectivity for the
canonical multiplication map `I ⊗[R] M →ₗ[R] M`.  It is independent of
flatness and quotient presentations, so all such arguments can reuse the same
universe bridge.
-/

@[expose] public section

universe u v w

namespace Ideal

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Injectivity of ideal tensor multiplication is preserved by lifting the module universe. -/
theorem tensorMul_injective_ulift (I : Ideal R)
    (h : Function.Injective (I.tensorMul M)) :
    Function.Injective (I.tensorMul (ULift.{w} M)) := sorry

/-- Injectivity of ideal tensor multiplication descends from a lifted module universe. -/
theorem tensorMul_injective_of_ulift (I : Ideal R)
    (h : Function.Injective (I.tensorMul (ULift.{w} M))) :
    Function.Injective (I.tensorMul M) := sorry

/-- Ideal tensor multiplication is injective exactly when it is injective after lifting the
module universe. -/
theorem tensorMul_injective_iff_ulift (I : Ideal R) :
    Function.Injective (I.tensorMul M) ↔
      Function.Injective (I.tensorMul (ULift.{w} M)) := sorry

end Ideal
