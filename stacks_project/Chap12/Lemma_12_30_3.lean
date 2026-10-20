module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Biproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uI vI uC vC

variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

variable [IsIdempotentComplete C] (F G : I ⥤ C)

/- Lemma 12.30.3 [0A2G]: a pointwise binary biproduct of filtered diagrams into an additive,
idempotent-complete category is essentially constant exactly when both summands are. -/
@[stacks 0A2G]
#check (IsFiltered.IsEssentiallyConstant.biprod_iff F G :
  IsFiltered.IsEssentiallyConstant (F ⊞ G) ↔
    IsFiltered.IsEssentiallyConstant F ∧ IsFiltered.IsEssentiallyConstant G)

/- The forward-independent construction is available separately: two essentially constant
filtered diagrams have an essentially constant pointwise binary biproduct. -/
#check (IsFiltered.IsEssentiallyConstant.biprod (F := F) (G := G) :
  IsFiltered.IsEssentiallyConstant F → IsFiltered.IsEssentiallyConstant G →
    IsFiltered.IsEssentiallyConstant (F ⊞ G))

/- The shared owner supplies the cofiltered dual at the same abstraction layer. -/
#check IsCofiltered.IsEssentiallyConstant.biprod_iff
