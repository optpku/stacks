module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.Etale
import StacksCheckRecall

/-!
# Étale inverse image as the right adjoint of finite-support lower shriek

Lemma 63.6.2: for an étale morphism `j : U ⟶ X`, uniqueness of adjoints
identifies the right adjoint of finite-support `lowerShriek j` with étale
restriction, so `j^!` agrees with `j⁻¹`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/- Lemma 63.6.2: For an étale morphism `j : U ⟶ X`, non-derived upper shriek
is canonically naturally isomorphic to inverse image on abelian étale sheaves. -/
@[stacks 0F5A] #check
  (AlgebraicGeometry.Scheme.Etale.upperShriekIsoRestriction j :
    upperShriek j ≅ etaleRestrictionSheaf j AddCommGrpCat.{u})

end AlgebraicGeometry.Scheme.Etale

end
