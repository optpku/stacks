/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.Etale.Composition
import StacksCheckRecall

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

variable {U X V : Scheme.{u}} (j : U ⟶ X) (j' : V ⟶ U) [Etale j] [Etale j']
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (j' ≫ j)).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/- Lemma 63.6.4: For composable étale morphisms, composition of inverse images
and composition of upper shrieks agree under the canonical identifications of
étale upper shriek with restriction. -/
@[stacks 0F5C] #check
  (AlgebraicGeometry.Scheme.Etale.upperShriekCompIso_restriction j j' :
    (upperShriekCompIso j' j).hom ≫
        whiskerRight (upperShriekIsoRestriction j).hom (upperShriek j') ≫
        whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (upperShriekIsoRestriction j').hom =
      (upperShriekIsoRestriction (j' ≫ j)).hom ≫
        (AlgebraicGeometry.Scheme.etaleRestrictionSheafCompIso j j' AddCommGrpCat.{u}).hom)

end
