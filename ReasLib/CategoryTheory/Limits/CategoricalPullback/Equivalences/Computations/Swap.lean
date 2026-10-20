/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Swap

/-!
# Structural computations for swapping categorical pullbacks

Comparison-map formulas for the symmetry exchanging the two legs of a categorical pullback.
-/

@[expose] public section

namespace CategoryTheory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
namespace Limits.CategoricalPullback
section EquivalenceTransportComputations
variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]
/-- Swapping a categorical pullback uses the inverse of its original structural
comparison as the new forward comparison map. -/
@[simp]
theorem swap.obj.iso.hom
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap F G).obj x).iso.hom = x.iso.inv := sorry

/-- Swapping a categorical pullback uses the original structural forward map as the
new inverse comparison map. -/
@[simp]
theorem swap.obj.iso.inv
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((swap F G).obj x).iso.inv = x.iso.hom := sorry


end EquivalenceTransportComputations
end Limits.CategoricalPullback
end CategoryTheory
