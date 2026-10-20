module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Retract

/-!
# Binary Biproducts of Essentially Constant Diagrams

Presentation-wise essential constancy is closed under pointwise binary biproducts.  In an
idempotent-complete target it is also stable under retracts, so a binary biproduct diagram is
essentially constant exactly when both summands are.  The cofiltered statements are provided at
the same layer rather than being left to downstream dualization.
-/

@[expose] public section

open CategoryTheory.Limits

universe uI vI uC vC

namespace CategoryTheory

section Filtered

variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
variable {C : Type uC} [Category.{vC} C]

namespace IsFiltered.IsEssentiallyConstant

variable [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The pointwise binary biproduct of two essentially constant filtered diagrams is essentially
constant. -/
theorem biprod {F G : I ⥤ C} (hF : IsFiltered.IsEssentiallyConstant F)
    (hG : IsFiltered.IsEssentiallyConstant G) :
    IsFiltered.IsEssentiallyConstant (F ⊞ G) := sorry

/-- A pointwise binary biproduct diagram into an idempotent-complete category is essentially
constant exactly when both summands are essentially constant. -/
@[stacks 0A2G "essential constancy and binary biproducts"]
theorem biprod_iff [IsIdempotentComplete C] (F G : I ⥤ C) :
    IsFiltered.IsEssentiallyConstant (F ⊞ G) ↔
      IsFiltered.IsEssentiallyConstant F ∧ IsFiltered.IsEssentiallyConstant G := sorry

end IsFiltered.IsEssentiallyConstant

end Filtered

section Cofiltered

variable {I : Type uI} [Category.{vI} I] [IsCofiltered I]
variable {C : Type uC} [Category.{vC} C]

namespace IsCofiltered.IsEssentiallyConstant

variable [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The pointwise binary biproduct of two essentially constant cofiltered diagrams is essentially
constant. -/
theorem biprod {F G : I ⥤ C} (hF : IsCofiltered.IsEssentiallyConstant F)
    (hG : IsCofiltered.IsEssentiallyConstant G) :
    IsCofiltered.IsEssentiallyConstant (F ⊞ G) := sorry

/-- A pointwise binary biproduct diagram into an idempotent-complete category is essentially
constant exactly when both summands are essentially constant. -/
theorem biprod_iff [IsIdempotentComplete C] (F G : I ⥤ C) :
    IsCofiltered.IsEssentiallyConstant (F ⊞ G) ↔
      IsCofiltered.IsEssentiallyConstant F ∧ IsCofiltered.IsEssentiallyConstant G := sorry

end IsCofiltered.IsEssentiallyConstant

end Cofiltered

end CategoryTheory
