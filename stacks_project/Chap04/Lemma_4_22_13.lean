/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Final
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I] [IsCofiltered I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (H : I ⥤ J) [H.Initial] (M : J ⥤ C)

/- Lemma 4.22.13: essential constancy of a cofiltered diagram is invariant under restriction
along an initial functor. -/
@[stacks 0A1T]
#check (IsCofiltered.IsEssentiallyConstant.iff_comp_initial H M :
  IsCofiltered.IsEssentiallyConstant M ↔ IsCofiltered.IsEssentiallyConstant (H ⋙ M))

end CategoryTheory
