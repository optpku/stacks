/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Exhaustive
public import ReasLib.CategoryTheory.Filtration.GradedPiece
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

/-- A finite decreasing filtration is filtered injective when every graded piece is injective
in the ambient category. -/
def IsFilteredInjective (A : C)
    (F : {F : DecreasingFiltration A // IndexedFiltration.IsFinite F}) : Prop :=
  ∀ p : ℤ, Injective (F.val.gradedPiece p)

/-- A finite decreasing filtration is filtered injective exactly when all its graded pieces are
injective. -/
theorem isFilteredInjective_iff (A : C)
    (F : {F : DecreasingFiltration A // IndexedFiltration.IsFinite F}) :
    IsFilteredInjective A F ↔ ∀ p : ℤ, Injective (F.val.gradedPiece p) :=
  Iff.rfl

end Finite

end DecreasingFiltration

end CategoryTheory
