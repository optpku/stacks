/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# The quotient sequence of a linear map

For a linear map `f : M →ₗ[R] N` and a submodule `q : Submodule R N`, this file packages the
canonical short exact sequence

`0 ⟶ M ⧸ q.comap f ⟶ N ⧸ q ⟶ N ⧸ (q ⊔ LinearMap.range f) ⟶ 0`.

The raw maps, their elementwise formulas, ordinary exactness, and the `ModuleCat` short complex
are exposed separately.  Ideal-colon sequences and other concrete applications can therefore use
the linear-algebra owner without rebuilding quotient maps.

@stack 0G1N
-/

@[expose] public section

open CategoryTheory

universe u v

namespace LinearMap.QuotientSequence

variable {R : Type u} [Ring R]
variable {M N : Type v} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- The injective map from the quotient by the full preimage of `q` to the quotient by `q`. -/
@[stacks 0G1N "general quotient-sequence inclusion"]
def inclusion (f : M →ₗ[R] N) (q : Submodule R N) :
    M ⧸ q.comap f →ₗ[R] N ⧸ q :=
  (q.comap f).mapQ q f le_rfl

/-- The terminal projection from `N ⧸ q` after adjoining the range of `f` to `q`. -/
@[stacks 0G1N "general quotient-sequence projection"]
def projection (f : M →ₗ[R] N) (q : Submodule R N) :
    N ⧸ q →ₗ[R] N ⧸ (q ⊔ LinearMap.range f) :=
  Submodule.factor le_sup_left

/-- The quotient-sequence inclusion sends the class of `m` to the class of `f m`. -/
@[simp, stacks 0G1N "general quotient-sequence inclusion formula"]
theorem inclusion_mk (f : M →ₗ[R] N) (q : Submodule R N) (m : M) :
    inclusion f q (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) := sorry

/-- The terminal quotient projection preserves representatives. -/
@[simp, stacks 0G1N "general quotient-sequence projection formula"]
theorem projection_mk (f : M →ₗ[R] N) (q : Submodule R N) (n : N) :
    projection f q (Submodule.Quotient.mk n) = Submodule.Quotient.mk n := sorry

/-- The two maps in the quotient sequence compose to zero. -/
@[stacks 0G1N "general quotient-sequence complex relation"]
theorem projection_comp_inclusion (f : M →ₗ[R] N) (q : Submodule R N) :
    (projection f q).comp (inclusion f q) = 0 := sorry

/-- The `ModuleCat` short complex associated to a linear map and a target submodule. -/
@[stacks 0G1N "general quotient short complex"]
def shortComplex (f : M →ₗ[R] N) (q : Submodule R N) :
    ShortComplex (ModuleCat.{v} R) :=
  ModuleCat.shortComplexOfCompEqZero
    (inclusion f q) (projection f q) (projection_comp_inclusion f q)

/-- The inclusion in the quotient sequence is injective. -/
@[stacks 0G1N "general quotient-sequence injectivity"]
theorem inclusion_injective (f : M →ₗ[R] N) (q : Submodule R N) :
    Function.Injective (inclusion f q) := sorry

/-- The two quotient maps are exact as functions. -/
@[stacks 0G1N "general quotient-sequence exactness"]
theorem exact (f : M →ₗ[R] N) (q : Submodule R N) :
    Function.Exact (inclusion f q) (projection f q) := sorry

/-- The terminal projection in the quotient sequence is surjective. -/
@[stacks 0G1N "general quotient-sequence surjectivity"]
theorem projection_surjective (f : M →ₗ[R] N) (q : Submodule R N) :
    Function.Surjective (projection f q) := sorry

/-- The quotient sequence attached to a linear map and a target submodule is short exact. -/
@[stacks 0G1N "general quotient short exact sequence"]
theorem shortExact (f : M →ₗ[R] N) (q : Submodule R N) :
    (shortComplex f q).ShortExact := sorry

end LinearMap.QuotientSequence
