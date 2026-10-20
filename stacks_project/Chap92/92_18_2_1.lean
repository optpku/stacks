/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.CommSq
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {A B A' B' : Sheaf J CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/- 92.18.2.1: a commutative square of sheaves of rings on a site C,
with vertices A, B, A', B' and arrows α : A ⟶ B, ρ : A ⟶ A',
β : A' ⟶ B', φ : B ⟶ B'. -/
@[stacks 08ST] #check
  (CategoryTheory.commSq_iff ρ α β φ : CommSq ρ α β φ ↔ ρ ≫ β = α ≫ φ)
