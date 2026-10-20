/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import ReasLib.CategoryTheory.CommSq
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {A B A' B' : CommRingCat.{u}}
variable {α : A ⟶ B} {ρ : A ⟶ A'} {β : A' ⟶ B'} {φ : B ⟶ B'}

/- 92.6.0.1: a commutative square of ring maps with vertices A, B, A', B'
and arrows α : A ⟶ B, ρ : A ⟶ A', β : A' ⟶ B', φ : B ⟶ B'. -/
@[stacks 08QM] #check
  (CategoryTheory.commSq_iff ρ α β φ :
    CategoryTheory.CommSq ρ α β φ ↔ ρ ≫ β = α ≫ φ)
