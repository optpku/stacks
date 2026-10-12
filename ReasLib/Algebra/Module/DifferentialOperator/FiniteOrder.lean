/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-Order Differential Endomorphisms

This leaf packages the endomorphisms of a module that have some finite
differential-operator order into their natural subring.  The construction only
depends on the commuting scalar action used by the order predicate; algebra
towers enter later, only for scalar-extension applications.

@stack 0H95
-/

@[expose] public section

universe u v w

namespace DifferentialOperator

section FiniteOrderEndomorphisms

variable {R : Type u} {S : Type v} {M : Type w}
variable [Semiring R] [AddCommGroup M] [Module R M]
variable [DistribSMul S M] [SMulCommClass S R M]

/-- The subring of `Module.End R M` consisting of endomorphisms with some finite
differential-operator order relative to the scalar action of `S`. -/
@[stacks 0H95]
def finiteOrderEndomorphisms : Subring (Module.End R M) where
  carrier := { D | ∃ k : ℕ, D.IsDifferentialOperatorOfOrder S k }
  zero_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry
  mul_mem' := sorry

/-- Membership in the finite-order differential endomorphism ring is exactly the existence of
an order bound. -/
@[simp]
theorem mem_finiteOrderEndomorphisms_iff (D : Module.End R M) :
    D ∈ finiteOrderEndomorphisms (R := R) (S := S) (M := M) ↔
      ∃ k : ℕ, D.IsDifferentialOperatorOfOrder S k := sorry

end FiniteOrderEndomorphisms

namespace FiniteOrderEndomorphisms

section ScalarAction

variable {R : Type u} {S : Type v} {M : Type w}
variable [Semiring R] [Semiring S] [AddCommGroup M]
variable [Module R M] [Module S M]
variable [SMulCommClass S R M] [SMulCommClass S S M]

/-- The ring homomorphism sending `s : S` to scalar multiplication by `s` in the finite-order
differential endomorphism ring. -/
@[stacks 0H95]
def smulRingHom : S →+* finiteOrderEndomorphisms (R := R) (S := S) (M := M) :=
  (Module.toModuleEnd R M).codRestrict
    (finiteOrderEndomorphisms (R := R) (S := S) (M := M))
    fun s =>
      (mem_finiteOrderEndomorphisms_iff _).2
        ⟨0, LinearMap.isDifferentialOperatorOfOrder_smul (R := R) (M := M) s⟩

/-- Coercing the scalar map into ordinary endomorphisms recovers scalar multiplication. -/
@[simp]
theorem coe_smulRingHom (s : S) :
    ((smulRingHom (R := R) (S := S) (M := M) s :
        finiteOrderEndomorphisms (R := R) (S := S) (M := M)) : Module.End R M) =
      DistribSMul.toLinearMap R M s := sorry

end ScalarAction

end FiniteOrderEndomorphisms

end DifferentialOperator
