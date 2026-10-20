module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.ExtensionByZero
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/- Lemma 63.4.3: The canonical graph comparison identifies étale extension by
zero with the sheafification of finite-support lower shriek, naturally in
abelian étale sheaves on U. -/
@[stacks 0F6Q] #check
  (AlgebraicGeometry.Scheme.Etale.extensionByZeroIsoLowerShriek j :
    Scheme.abelianExtensionByZero j ≅
      lowerShriekPresheaf j ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Etale.extensionByZeroToLowerShriekPresheaf j :
  sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (etaleRestriction j).op.lan ⟶
    lowerShriekPresheaf j)

end
