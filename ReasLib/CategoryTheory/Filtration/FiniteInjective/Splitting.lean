/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Splitting Strict Maps from Finite Filtered-Injective Objects

Finite support lets one split a strict monomorphism one associated graded piece at a time. The
result is exposed on the filtered-injective owner rather than through the inductive construction
used by a particular proof.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C] [Abelian C]

/-- A strict monomorphism from a finite filtered-injective object is a split monomorphism. -/
@[stacks 05TQ]
theorem splitMono {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj]
    {A : FilteredObject C} (u : I.obj ⟶ A) [Mono u.hom]
    (hu : FilteredObject.Hom.Strict u) : IsSplitMono u := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective
