/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural numbers acting on integers

Natural numbers act on integers by translation through the additive homomorphism `ℕ →+ ℤ`.
This action is independent of graded rings and modules, so it lives at the group-action layer.
-/

@[expose] public section

namespace AddAction

/-
API design: the `AddAction` is the sole global data owner; its inherited `VAdd` supplies `+ᵥ`.
Defining the action by `compHom` exposes the canonical additive map and avoids a second standalone
`VAdd` instance whose definitional equality could depend on import order.
-/

/-- Natural numbers act on integers by addition through the canonical cast `ℕ → ℤ`. -/
@[stacks 01CV "natural numbers acting on integers"]
instance natInt : AddAction ℕ ℤ :=
  AddAction.compHom ℤ Int.ofNatHom.toAddMonoidHom

/-- Natural translation on integers is cancellative in both the scalar and point arguments. -/
@[stacks 01CV "cancellative natural-to-integer translation"]
instance natIntIsCancel : IsCancelVAdd ℕ ℤ := sorry

/-- Natural translation is injective in the integer point. -/
@[stacks 01CV "integer-point injectivity of natural translation"]
theorem nat_vadd_int_point_injective (n : ℕ) :
    Function.Injective (fun i : ℤ => n +ᵥ i) := sorry

/-- Natural translation is injective in the natural scalar. -/
@[stacks 01CV "natural-scalar injectivity of translation"]
theorem nat_vadd_int_scalar_injective (i : ℤ) :
    Function.Injective (fun n : ℕ => n +ᵥ i) := sorry

/-- Natural-number translation on integers is ordinary addition after casting. -/
@[stacks 01CV "natural-to-integer translation formula", simp]
theorem nat_vadd_int (n : ℕ) (i : ℤ) :
    n +ᵥ i = (n : ℤ) + i := sorry

/-- Casting a natural number to an integer commutes with natural translation. -/
@[stacks 01CV "equivariance of the natural-to-integer cast"]
theorem ofNat_vadd (m n : ℕ) :
    Int.ofNat (m +ᵥ n) = m +ᵥ Int.ofNat n := sorry

/-- The natural-number cast into `ℤ`, bundled as a map equivariant for natural translation. -/
@[stacks 01CV "equivariant natural-number inclusion into integers"]
def natIntHom : AddActionHom (id : ℕ → ℕ) ℕ ℤ where
  toFun := Int.ofNat
  map_vadd' := ofNat_vadd

/-- The equivariant natural-number inclusion evaluates to the usual integer cast. -/
@[stacks 01CV "equivariant natural-number inclusion formula", simp]
theorem natIntHom_apply (n : ℕ) :
    natIntHom n = (n : ℤ) := sorry

end AddAction


