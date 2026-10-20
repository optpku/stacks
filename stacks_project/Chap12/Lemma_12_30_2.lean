module

public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uJ vJ uC vC

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

variable [IsIdempotentComplete C] (F G : J ⥤ C)

/- Lemma 12.30.2 (1) [0A2F]: in an additive, idempotent-complete category, a pointwise binary
biproduct diagram admits a colimit exactly when both summands do. -/
@[stacks 0A2F]
#check (hasColimit_biprod_iff F G :
  HasColimit (F ⊞ G) ↔ HasColimit F ∧ HasColimit G)

/- Lemma 12.30.2 (2) [0A2F]: in the existence case, the canonical comparison identifies the
colimit of the pointwise biproduct with the biproduct of the two colimits. -/
section

variable [HasColimit F] [HasColimit G]

@[stacks 0A2F]
#check (colimitBiprodIso F G : colimit (F ⊞ G) ≅ colimit F ⊞ colimit G)

/- Its component formula makes the comparison directly usable in downstream cocone arguments. -/
#check colimitBiprodIso_ι_hom F G

end
