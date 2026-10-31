/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Injective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Filtered Injectivity for Finite Filtrations

This module defines filtered injectivity for a finite decreasing filtration by
requiring each graded piece to be injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace DecreasingFiltration

namespace Finite

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasCokernels C]

/-- Filtered injectivity for a finite filtered object is the canonical filtered-object predicate.

This is a thin specialization: the finite subcategory carries an underlying `FilteredObject`,
and filtered injectivity is owned by `FilteredObject.IsFilteredInjective`. -/
abbrev IsFilteredInjective (I : FilteredObject.Finite.category C) : Prop :=
  FilteredObject.IsFilteredInjective I.obj

/-- A finite decreasing filtration is filtered injective exactly when all its graded pieces are
injective. -/
theorem isFilteredInjective_iff (I : FilteredObject.Finite.category C) :
    IsFilteredInjective I ↔ ∀ p : ℤ, Injective (I.obj.gradedPiece p) :=
  ⟨fun h p => h.injective p, fun h => ⟨h⟩⟩

end Finite

end DecreasingFiltration

end CategoryTheory
