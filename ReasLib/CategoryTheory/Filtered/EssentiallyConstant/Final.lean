/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Final
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram

/-!
# Essentially constant diagrams and final functors

Presentation-wise essential constancy is invariant under restriction along a final functor.
The dual initial-functor statement is exposed alongside it so filtered and cofiltered
applications use the same API shape.
-/

@[expose] public section

universe uI vI uJ vJ uC vC

namespace CategoryTheory

namespace IsFiltered.IsEssentiallyConstant

/-- Essential constancy of a filtered diagram is invariant under restriction along a final
functor.  Filteredness of the target indexing category follows from finality and is not an
additional input. -/
@[stacks 0A1S "essential constancy under a final functor"]
theorem iff_comp_final {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] (M : J ⥤ C) :
    IsFiltered.IsEssentiallyConstant M ↔
      IsFiltered.IsEssentiallyConstant (H ⋙ M) := sorry

end IsFiltered.IsEssentiallyConstant

namespace IsCofiltered.IsEssentiallyConstant

/-- Essential constancy of a cofiltered diagram is invariant under restriction along an initial
functor.  Cofilteredness of the target indexing category follows from initiality. -/
@[stacks 0A1T "essential constancy under an initial functor"]
theorem iff_comp_initial {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsCofiltered.IsEssentiallyConstant M ↔
      IsCofiltered.IsEssentiallyConstant (H ⋙ M) := sorry

end IsCofiltered.IsEssentiallyConstant

end CategoryTheory
