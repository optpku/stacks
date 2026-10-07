module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.FullSubsite
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.StandardTopology

section Nested

variable (τ : StandardTopology) (X : Scheme.{u})
variable (P₁ P₂ : ObjectProperty (Over X)) [IsFullSubsite τ X P₁] [IsFullSubsite τ X P₂]
variable (hP : P₁ ≤ P₂)

/- Lemma 59.49.2 (1): the inclusion of the nested full subcategories is fully faithful. -/
@[stacks 07AJ]
#check (AlgebraicGeometry.StandardTopology.fullSubsiteInclusionFullyFaithful hP :
  (P₁.ιOfLE hP).FullyFaithful)

/- Lemma 59.49.2 (2): the inclusion of the nested full subsites is continuous. -/
@[stacks 07AJ]
#check (AlgebraicGeometry.StandardTopology.fullSubsiteInclusionContinuous τ X P₁ P₂ hP :
    (P₁.ιOfLE hP).IsContinuous
      (P₁.ι.restrictedTopology (τ.overTopology X))
      (P₂.ι.restrictedTopology (τ.overTopology X)))

/- Lemma 59.49.2 (3): the inclusion of the nested full subsites is cocontinuous. -/
@[stacks 07AJ]
#check (AlgebraicGeometry.StandardTopology.fullSubsiteInclusionCocontinuous τ X P₁ P₂ hP :
    (P₁.ιOfLE hP).IsCocontinuous
      (P₁.ι.restrictedTopology (τ.overTopology X))
      (P₂.ι.restrictedTopology (τ.overTopology X)))

/- Lemma 59.49.2 (4): the canonical map from lower shriek of the structure sheaf on the
smaller full subsite to the structure sheaf on the larger full subsite is an isomorphism. -/
@[stacks 07AJ]
#check (AlgebraicGeometry.StandardTopology.lowerShriekStructureSheafMap_isIso τ X P₁ P₂ hP :
  IsIso (IsFullSubsite.lowerShriekStructureSheafMap τ X P₁ P₂ hP))

end Nested

end AlgebraicGeometry.StandardTopology
