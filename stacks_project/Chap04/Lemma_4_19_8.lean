/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.Components
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {I : Type u} [Category.{v} I] [HasSpanCocones I]
variable (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
  ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
variable (j : ConnectedComponents I)

/- Lemma 4.19.8: span cocones and postcomposition equalizers make every canonical connected
component filtered. -/
@[stacks 002X]
#check (ConnectedComponents.component.isFiltered_of_postcomposition hMap j :
  IsFiltered j.Component)

/- The neutral class-based form makes the component result directly available to typeclass
search. -/
#check CategoryTheory.ConnectedComponents.component.isFiltered

end CategoryTheory
