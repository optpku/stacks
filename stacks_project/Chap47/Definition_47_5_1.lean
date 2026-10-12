/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.Hull
import StacksCheckRecall

@[expose] public section

universe u v w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {I : Type w} [AddCommGroup I] [Module R I] [Module.Injective R I]

/- Definition 47.5.1: An injection `f : M →ₗ[R] I` is an injective hull if `I` is an
injective `R`-module and the range of `f` is essential in `I`. -/
@[stacks 08Y2] #check (LinearMap.IsInjectiveHull : (M →ₗ[R] I) → Prop)
