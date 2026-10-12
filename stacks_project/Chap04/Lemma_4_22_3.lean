/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits.Comparison
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe vI uI vC uC

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

section

variable [IsFiltered I]
variable {M : I ⥤ C} (hM : IsFiltered.IsEssentiallyConstant M)

/- Lemma 4.22.3 (1): an essentially constant filtered system has the displayed constant value as
its colimit. -/
@[stacks 0G2V "filtered colimit value"]
#check (IsFiltered.IsEssentiallyConstant.exists_colimitCocone hM :
  ∃ c : ColimitCocone M, c.cocone.IsEssentiallyConstant)

end


section

variable [IsCofiltered I]
variable {M : I ⥤ C} (hM : IsCofiltered.IsEssentiallyConstant M)

/- Lemma 4.22.3 (2): an essentially constant cofiltered system has the displayed constant value
as its limit. -/
@[stacks 0G2V "cofiltered limit value"]
#check (IsCofiltered.IsEssentiallyConstant.exists_limitCone hM :
  ∃ c : LimitCone M, c.cone.IsEssentiallyConstant)

end

end CategoryTheory
