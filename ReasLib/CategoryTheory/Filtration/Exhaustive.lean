/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Indexed

/-!
# Exhaustive and Separated Filtrations

A decreasing filtration is exhaustive if the union of its stages is the whole object, and
separated if their intersection is zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IndexedFiltration

variable {I : Type*} [Preorder I] {A : C}

/-- A filtration is exhaustive if the whole object is the smallest subobject containing every
stage. -/
def IsExhaustive (F : IndexedFiltration I A) : Prop :=
  ∀ Y : Subobject A, (∀ i : I, F.stage i ≤ Y) → ⊤ ≤ Y

end IndexedFiltration

section ZeroObject

variable [HasZeroObject C] {I : Type*} [Preorder I] {A : C}

namespace IndexedFiltration

/-- A filtration is separated if the zero subobject is the largest subobject contained in
every stage. -/
def IsSeparated (F : IndexedFiltration I A) : Prop :=
  ∀ Y : Subobject A, (∀ i : I, Y ≤ F.stage i) → Y ≤ ⊥

/-- A filtration is finite if some stage is the whole object and some stage is zero. -/
def IsFinite (F : IndexedFiltration I A) : Prop :=
  ∃ n m : I, F.stage n = ⊤ ∧ F.stage m = ⊥

end IndexedFiltration

end ZeroObject

end CategoryTheory
