/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Product

/-!
# Finite Modules over Product Semirings

This file records the module-theoretic finite-generation criterion for product semirings.  It is
independent of bundled module categories, so it can be used directly in algebraic and homological
arguments.
-/

@[expose] public section

universe u v w

namespace Module.Product

variable (R : Type u) (S : Type v) [Semiring R] [Semiring S]

private def leftScalarMap (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Module.Product.leftSubmodule R S M →ₛₗ[RingHom.fst R S]
      Module.Product.leftSubmodule R S M where
  toFun := id
  map_add' := by intros; rfl
  map_smul' := by
    intro a m
    apply Subtype.ext
    exact Module.Product.leftSubmodule_smul_val R S M a m

private def rightScalarMap (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Module.Product.rightSubmodule R S M →ₛₗ[RingHom.snd R S]
      Module.Product.rightSubmodule R S M where
  toFun := id
  map_add' := by intros; rfl
  map_smul' := by
    intro a m
    apply Subtype.ext
    exact Module.Product.rightSubmodule_smul_val R S M a m

/-- A module over a product semiring is finite exactly when its two idempotent factors are finite
over the corresponding factors. -/
@[stacks 00JH "finite product semiring module criterion"]
theorem finite_iff (M : Type w) [AddCommMonoid M] [Module (R × S) M] :
    Module.Finite (R × S) M ↔
      Module.Finite R (leftSubmodule R S M) ∧ Module.Finite S (rightSubmodule R S M) := by
  let L := leftSubmodule R S M
  let Q := rightSubmodule R S M
  have hleft : Module.Finite (R × S) L ↔ Module.Finite R L :=
    LinearMap.finite_iff_of_bijective (leftScalarMap R S M)
      ⟨Function.injective_id, Function.surjective_id⟩
  have hright : Module.Finite (R × S) Q ↔ Module.Finite S Q :=
    LinearMap.finite_iff_of_bijective (rightScalarMap R S M)
      ⟨Function.injective_id, Function.surjective_id⟩
  constructor
  · intro hM
    letI : Module.Finite (R × S) M := hM
    letI : Module.Finite (R × S) (L × Q) :=
      Module.Finite.equiv (factorLinearEquiv R S M)
    have hL : Module.Finite (R × S) L :=
      Module.Finite.of_surjective (LinearMap.fst (R × S) L Q)
        (LinearMap.fst_surjective (R := R × S) (M := L) (M₂ := Q))
    have hQ : Module.Finite (R × S) Q :=
      Module.Finite.of_surjective (LinearMap.snd (R × S) L Q)
        (LinearMap.snd_surjective (R := R × S) (M := L) (M₂ := Q))
    exact ⟨hleft.mp hL, hright.mp hQ⟩
  · rintro ⟨hL, hQ⟩
    letI : Module.Finite (R × S) L := hleft.mpr hL
    letI : Module.Finite (R × S) Q := hright.mpr hQ
    letI : Module.Finite (R × S) (L × Q) := inferInstance
    exact Module.Finite.equiv (factorLinearEquiv R S M).symm

end Module.Product
