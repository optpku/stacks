/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits
public import ReasLib.CategoryTheory.Limits.Retract

/-!
# Retracts of Essentially Constant Diagrams

Presentation-wise essential constancy is stable under retracts of filtered diagrams when the
target category is idempotent complete.  The cofiltered instance records the dual fact.  Stating
these results as object-property instances lets generic retract and direct-summand APIs consume
them without local instance rebuilding.
-/

@[expose] public section

open CategoryTheory.ObjectProperty

universe uI vI uC vC

namespace CategoryTheory

section Filtered

variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
variable {C : Type uC} [Category.{vC} C]

namespace IsFiltered.IsEssentiallyConstant

/-- Essential constancy of filtered diagrams is stable under retracts when the target is
idempotent complete. -/
instance isStableUnderRetracts [IsIdempotentComplete C] :
    IsStableUnderRetracts (fun F : I ⥤ C ↦ IsFiltered.IsEssentiallyConstant F) := sorry

end IsFiltered.IsEssentiallyConstant

end Filtered

section Cofiltered

variable {I : Type uI} [Category.{vI} I] [IsCofiltered I]
variable {C : Type uC} [Category.{vC} C]

namespace IsCofiltered.IsEssentiallyConstant

/-- Essential constancy of cofiltered diagrams is stable under retracts when the target is
idempotent complete. -/
instance isStableUnderRetracts [IsIdempotentComplete C] :
    IsStableUnderRetracts (fun F : I ⥤ C ↦ IsCofiltered.IsEssentiallyConstant F) := sorry

end IsCofiltered.IsEssentiallyConstant

end Cofiltered

end CategoryTheory
