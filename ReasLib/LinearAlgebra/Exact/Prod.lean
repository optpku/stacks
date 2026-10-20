/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact pairs stabilized by a product summand

This leaf records the two linear-algebra facts needed to stabilize the left
side of an exact pair by a common direct summand.
-/

@[expose] public section

universe u v w x y

namespace Function

variable {R : Type u} {F : Type v} {M : Type w} {N : Type x} {P : Type y}
variable [Semiring R] [AddCommMonoid F] [AddCommMonoid M] [AddCommMonoid N]
variable [AddCommMonoid P] [Module R F] [Module R M] [Module R N] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- Adjoining the same left product summand to the first two terms of an exact
pair preserves exactness. -/
@[stacks 07EX "exactness after adjoining a common left summand"]
theorem Exact.prod_left (h : Exact f g) :
    Exact ((LinearMap.id : F →ₗ[R] F).prodMap f)
      (g ∘ₗ LinearMap.snd R F N) := sorry

/-- Precomposing a surjective linear map with the second projection remains
surjective. -/
@[stacks 07EX "surjectivity after adjoining a source summand"]
theorem Surjective.comp_snd (hg : Surjective g) :
    Surjective (g ∘ₗ LinearMap.snd R F N) := sorry

end Function
