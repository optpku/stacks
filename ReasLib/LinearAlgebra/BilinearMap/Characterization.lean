/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Characterizing unbundled bilinear maps

The preferred data owner remains `M →ₗ[R] N →ₗ[R] P`.  This leaf provides a
small predicate-level bridge for functions that are presented unbundled and
must be checked one argument at a time.
-/

universe u v w x

namespace IsBilinearMap

variable {R : Type u} {M : Type v} {N : Type w} {P : Type x}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- A two-variable function is bilinear exactly when each partial function is
linear. -/
@[stacks 00CW "bilinearity by partial linearity"]
theorem iff_isLinearMap {f : M → N → P} :
    IsBilinearMap R f ↔
      (∀ x : M, IsLinearMap R (f x)) ∧
        ∀ y : N, IsLinearMap R (fun x ↦ f x y) := sorry
/- Proof strategy: use `IsBilinearMap.toLinearMap` in the forward direction;
in the reverse direction, assemble the four structure fields from the two
families of `IsLinearMap` laws. -/

/-- A function on a product is bilinear after currying exactly when its two
families of partial functions are linear. -/
@[stacks 00CW "product bilinearity by partial linearity"]
theorem iff_isLinearMap_curry {f : M × N → P} :
    IsBilinearMap R (Function.curry f) ↔
      (∀ x : M, IsLinearMap R (fun y ↦ f (x, y))) ∧
        ∀ y : N, IsLinearMap R (fun x ↦ f (x, y)) := sorry
/- Proof strategy: specialize `iff_isLinearMap` to `Function.curry f`. -/

end IsBilinearMap
