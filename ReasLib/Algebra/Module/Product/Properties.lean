/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite and Flat Factors of Product Modules

This leaf records the small product-projection consequences of Mathlib's generic transport
theorems.  The foundational facts remain `Module.Flat.of_retract` and
`Module.Finite.of_surjective`; these declarations package the frequent situation in which a
module is exhibited as an `R`-linear product.

This is independent of the product-semiring decomposition API in the sibling files: here the
base semiring is fixed and the product is a product of modules over that base.
-/

@[expose] public section

universe u v w x

namespace Module.Flat

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {P : Type x} [AddCommMonoid P] [Module R P]

/-- The first factor of a product decomposition of a flat module is flat. -/
@[stacks 00JH "flat module product first factor"]
theorem of_linearEquiv_prod_fst [Module.Flat R M] (e : M ≃ₗ[R] N × P) :
    Module.Flat R N := sorry

/-- The second factor of a product decomposition of a flat module is flat. -/
@[stacks 00JH "flat module product second factor"]
theorem of_linearEquiv_prod_snd [Module.Flat R M] (e : M ≃ₗ[R] N × P) :
    Module.Flat R P := sorry

end Module.Flat

namespace Module.Finite

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {P : Type x} [AddCommMonoid P] [Module R P]

/-- The first factor of a product decomposition of a finite module is finite. -/
@[stacks 00JH "finite module product first factor"]
theorem of_linearEquiv_prod_fst [Module.Finite R M] (e : M ≃ₗ[R] N × P) :
    Module.Finite R N := sorry

/-- The second factor of a product decomposition of a finite module is finite. -/
@[stacks 00JH "finite module product second factor"]
theorem of_linearEquiv_prod_snd [Module.Finite R M] (e : M ≃ₗ[R] N × P) :
    Module.Finite R P := sorry

end Module.Finite
