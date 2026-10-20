/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Filtered Objects in Weak Serre Classes

Finite filtrations let weak Serre membership be reconstructed from the graded pieces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace CategoryTheory
namespace DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C] {A : C}

/-- The ambient object of a finite filtration belongs to a weak Serre class whenever every
graded piece belongs to that class. -/
@[stacks 012W "finite filtration dévissage"]
theorem object_mem_of_isFinite (F : DecreasingFiltration A) (P : ObjectProperty C)
    [IsWeakSerreClass P] (hfinite : IndexedFiltration.IsFinite F)
    (hgraded : ∀ p : ℤ, P (F.gradedPiece p)) : P A := sorry

end DecreasingFiltration
end CategoryTheory
