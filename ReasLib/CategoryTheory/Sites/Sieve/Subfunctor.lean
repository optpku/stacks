/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sieves

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Sieve

universe u v

variable {C : Type u} [Category.{v} C] {U : C}

/-- The subfunctor of `yoneda.obj U` determined by a sieve on `U`. -/
def subfunctor (S : Sieve U) : Subfunctor (yoneda.obj U) where
  obj T := {f | S f}
  map f x hx := S.downward_closed hx f.unop

/-- The sieve on `U` determined by a subfunctor of `yoneda.obj U`. -/
def ofSubfunctor (R : Subfunctor (yoneda.obj U)) : Sieve U where
  arrows Y f := f ∈ R.obj (Opposite.op Y)
  downward_closed := by
    intro Y Z f hf g
    simpa using R.map g.op hf

/-- Membership in the subfunctor associated to a sieve is componentwise sieve membership. -/
@[simp] theorem mem_subfunctor (S : Sieve U) {T : Cᵒᵖ} (f : T.unop ⟶ U) :
    f ∈ (subfunctor S).obj T ↔ S f := Iff.rfl

/-- Membership in a sieve recovered from a subfunctor is componentwise subfunctor membership. -/
@[simp] theorem ofSubfunctor_apply (R : Subfunctor (yoneda.obj U)) {Y : C} (f : Y ⟶ U) :
    ofSubfunctor R f ↔ f ∈ R.obj (Opposite.op Y) := Iff.rfl

/-- Recovering a sieve from its associated subfunctor returns the original sieve. -/
theorem ofSubfunctor_subfunctor (S : Sieve U) : ofSubfunctor (subfunctor S) = S := sorry

/-- The subfunctor associated to a sieve recovered from a representable subfunctor is unchanged. -/
theorem subfunctor_ofSubfunctor (R : Subfunctor (yoneda.obj U)) : subfunctor (ofSubfunctor R) = R := sorry

/-- Sieves on `U` are equivalent to subfunctors of the representable `yoneda.obj U`. -/
def subfunctorEquiv (U : C) : Sieve U ≃ Subfunctor (yoneda.obj U) where
  toFun := subfunctor
  invFun := ofSubfunctor
  left_inv := ofSubfunctor_subfunctor
  right_inv := subfunctor_ofSubfunctor

end CategoryTheory.Sieve
