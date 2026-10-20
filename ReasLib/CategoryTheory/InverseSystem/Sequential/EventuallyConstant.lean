/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.InverseSystem.EventualIso
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Eventually constant sequential inverse systems

This leaf packages eventual constancy together with its eventual value and relates Mathlib's
cofiltered predicate to the transition maps of a sequential inverse system.
-/

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

/-- A sequential inverse system is eventually constant with value `X` when some stage is
isomorphic to `X` and all maps into that stage are eventually invertible. -/
@[stacks 0D6T "eventual value of a sequential inverse system"]
def IsEventuallyConstantWithValue (F : SequentialInverseSystem A) (X : A) : Prop :=
  ∃ n : ℕ, F.IsEventuallyConstantTo (op n) ∧ IsIsomorphic (F.obj (op n)) X

/-- On a sequential inverse system, eventual constancy at stage `N` is equivalent to
invertibility of every transition map from a later stage to `N`. -/
@[stacks 0D6T]
theorem isEventuallyConstantTo_iff_transitionMap_isIso
    (F : SequentialInverseSystem A) (N : ℕ) :
    F.IsEventuallyConstantTo (op N) ↔
      ∀ (n : ℕ) (hNn : N ≤ n), IsIso (F.transitionMap hNn) := sorry

/-- An eventual value can be exhibited by a stage and invertible transition maps into it. -/
@[stacks 0D6T]
theorem isEventuallyConstantWithValue_of_transitionMap_isIso
    (F : SequentialInverseSystem A) (X : A) (N : ℕ)
    (hX : IsIsomorphic (F.obj (op N)) X)
    (htransition : ∀ (n : ℕ) (hNn : N ≤ n), IsIso (F.transitionMap hNn)) :
    F.IsEventuallyConstantWithValue X := sorry

/-- An eventual value supplies a stage representing it together with all transition
isomorphisms into that stage. -/
@[stacks 0D6T]
theorem exists_stage_transitionMap_isIso
    {F : SequentialInverseSystem A} {X : A}
    (h : F.IsEventuallyConstantWithValue X) :
    ∃ N : ℕ, IsIsomorphic (F.obj (op N)) X ∧
      ∀ (n : ℕ) (hNn : N ≤ n), IsIso (F.transitionMap hNn) := sorry

/-- An eventual value is represented, up to isomorphism, by every sufficiently late stage. -/
@[stacks 0D6T]
theorem exists_late_isomorphic_to
    {F : SequentialInverseSystem A} {X : A}
    (h : F.IsEventuallyConstantWithValue X) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsIsomorphic (F.obj (op n)) X := sorry

end CategoryTheory.SequentialInverseSystem

end
