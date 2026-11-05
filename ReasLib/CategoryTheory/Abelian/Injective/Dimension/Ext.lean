/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import ReasLib.CategoryTheory.Abelian.Extension.Yoneda.Ext
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Injective Dimension from Ext Vanishing

This file packages fixed-target and uniform degreewise Ext-vanishing criteria
for strict bounds on injective dimension.
-/

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe w v u

namespace CategoryTheory.HasInjectiveDimensionLT

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Peel a degree-one factor off the source end of a positive-degree Ext class. -/
private theorem exists_comp_one {A B : C} (n : ℕ) (e : Ext B A (n + 1)) :
    ∃ (Z : C) (α : Ext B Z 1) (β : Ext Z A n), α.comp β (Nat.add_comm 1 n) = e := by
  induction n generalizing A B with
  | zero =>
    exact ⟨A, e, Ext.mk₀ (𝟙 A), e.comp_mk₀_id⟩
  | succ n ih =>
    let m : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    obtain ⟨E, rfl⟩ := YonedaExtension.toExt_surjective (A := A) (B := B) (m + 1) e
    rw [YonedaExtension.toExt_succ]
    obtain ⟨Z, α, β, hβ⟩ := ih (YonedaExtension.toExt (YonedaExtension.Quotient.obj E))
    refine ⟨Z, α, β.comp (YonedaExtension.Quotient.head E).extClass rfl, ?_⟩
    rw [← hβ]
    exact (Ext.comp_assoc α β _ (Nat.add_comm 1 n) rfl (by omega)).symm

/-- If every degree-`p` Ext group with fixed target `A` is subsingleton, then
`A` has injective dimension strictly less than `p`.

Yoneda representatives give the dimension-shifting step in any abelian category;
no enough-projectives or enough-injectives hypothesis is required. -/
theorem of_ext_vanishing
    (A : C) (p : ℕ) (hExt : ∀ B : C, Subsingleton (Ext B A p)) :
    HasInjectiveDimensionLT A p := by
  by_cases hp : p = 0
  · subst p
    apply Limits.IsZero.hasInjectiveDimensionLT_zero
    rw [Limits.IsZero.iff_id_eq_zero]
    apply Ext.homEquiv₀.symm.injective
    exact (hExt A).elim _ _
  refine HasInjectiveDimensionLT.mk ?_
  intro i hi B e
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction k generalizing B with
  | zero => exact (hExt B).elim _ _
  | succ k ih =>
    obtain ⟨Z, α, β, rfl⟩ := exists_comp_one (p + k) e
    rw [ih (by omega) β, Ext.comp_zero]

/-- Lemma 13.27.8 (Stacks `0EWW`): uniform vanishing of degree-`p` Ext groups
gives injective dimension strictly less than `p` for every target object in an arbitrary
abelian category. -/
@[stacks 0EWW]
theorem of_uniform_ext
    (p : ℕ) (hExt : ∀ A B : C, Subsingleton (Ext B A p)) (A : C) :
    HasInjectiveDimensionLT A p :=
  of_ext_vanishing A p (fun B ↦ hExt A B)

end CategoryTheory.HasInjectiveDimensionLT
