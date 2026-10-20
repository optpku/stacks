/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

universe vC uC w

namespace CategoryTheory

open Limits

namespace Functor

/-- A set-valued functor is Galois when its source category has finite limits
and colimits and finite connected coproduct decompositions, while the functor
has finite fibers, reflects isomorphisms, and is exact. -/
def IsGalois {C : Type uC} [Category.{vC} C] (F : C ⥤ Type w) : Prop :=
  HasFiniteLimits C ∧
    HasFiniteColimits C ∧
      (∀ X : C,
        ∃ (n : ℕ) (components : Fin n → C)
          (inclusions : ∀ index, components index ⟶ X),
          (∀ index, PreGaloisCategory.IsConnected (components index)) ∧
            Nonempty (IsColimit (Cofan.mk X inclusions))) ∧
        (∀ X : C, Finite (F.obj X)) ∧
          F.ReflectsIsomorphisms ∧ exactFunctor C (Type w) F

end Functor

end CategoryTheory
