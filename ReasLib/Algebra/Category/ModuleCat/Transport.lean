/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Transport of Linear Maps Between Module Objects

This leaf owns dependent transport of linear maps across equalities of codomain module objects.
The domain and codomain universes are independent.
-/

@[expose] public section

universe u v w

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Transport a linear map across an equality of codomain module objects. -/
def castLinearMap {M : ModuleCat.{w} R} {N N' : ModuleCat.{v} R}
    (h : N = N') (f : M →ₗ[R] N) : M →ₗ[R] N' :=
  match h with
  | rfl => f

/-- Transporting a linear map along reflexivity does nothing. -/
@[simp] theorem castLinearMap_rfl {M : ModuleCat.{w} R} {N : ModuleCat.{v} R}
    (f : M →ₗ[R] N) :
    castLinearMap rfl f = f := sorry

/-- Applying a transported linear map transports its output. -/
@[simp] theorem castLinearMap_apply {M : ModuleCat.{w} R} {N N' : ModuleCat.{v} R}
    (h : N = N') (f : M →ₗ[R] N) (x : M) :
    castLinearMap h f x =
      cast (congrArg (fun X : ModuleCat.{v} R ↦ (X : Type v)) h) (f x) := sorry

end ModuleCat
