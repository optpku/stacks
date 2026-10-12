/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stably free modules

@stack 0BC3

This file owns stable isomorphism and stable freeness independently of any
chapter-facing source file.
-/

universe u v w

namespace Module

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]

/-- Definition 15.3.1 (1): two modules are stably isomorphic when adjoining finite free summands
makes them linearly equivalent. -/
@[stacks 0BC3 "(1), stable isomorphism"]
def StablyIsomorphic : Prop :=
  ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (N × (Fin n → R)))

/-- Definition 15.3.1 (2): a module is stably free when it is stably isomorphic to a free module. -/
@[stacks 0BC3 "(2), stably free module"]
class StablyFree : Prop where
  /-- A free module stably isomorphic to the given module. -/
  exists_free :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F),
      StablyIsomorphic R M F

/-- Stable isomorphism is reflexive. -/
theorem stablyIsomorphic_refl : StablyIsomorphic R M M := sorry

/-- Every free module is stably free. -/
@[stacks 0BC3 "free modules are stably free"]
instance stablyFree_of_free [Module.Free R M] : StablyFree R M := sorry

namespace StablyFree

/-- An explicit freeness proof gives stable freeness without installing a local instance. -/
theorem of_free {R' : Type u} [Ring R'] {M' : Type v} [AddCommGroup M'] [Module R' M']
    (h : Module.Free R' M') : StablyFree R' M' := sorry

/-- Stable freeness transports across an `R`-linear equivalence. -/
theorem of_linearEquiv {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) [StablyFree R N] :
    StablyFree R M := sorry

end StablyFree

end Module

open CategoryTheory

/-- The object property of finite stably free `R`-modules. -/
@[stacks 0BC3 "finite stably free module property"]
abbrev finiteStablyFreeModuleProperty (R : Type u) [Ring R] : ObjectProperty (ModuleCat R) :=
  fun M ↦ Module.Finite R M ∧ Module.StablyFree R M
