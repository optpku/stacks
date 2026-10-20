/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Restriction.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

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

/-- For composable étale morphisms, the canonical composition isomorphism for
upper shriek agrees with restriction composition under the canonical
identifications of upper shriek with restriction. -/
theorem upperShriekCompIso_restriction :
    (upperShriekCompIso j' j).hom ≫
        whiskerRight (upperShriekIsoRestriction j).hom (upperShriek j') ≫
        whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (upperShriekIsoRestriction j').hom =
      (upperShriekIsoRestriction (j' ≫ j)).hom ≫
        (AlgebraicGeometry.Scheme.etaleRestrictionSheafCompIso j j' AddCommGrpCat.{u}).hom := sorry

/-- The canonical upper-shriek and restriction composition maps agree on every
abelian étale sheaf under the canonical identifications with restriction. -/
theorem upperShriekCompIso_restriction_app
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((upperShriekCompIso j' j).hom ≫
        whiskerRight (upperShriekIsoRestriction j).hom (upperShriek j') ≫
        whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (upperShriekIsoRestriction j').hom).app G =
      ((upperShriekIsoRestriction (j' ≫ j)).hom ≫
        (AlgebraicGeometry.Scheme.etaleRestrictionSheafCompIso j j'
          AddCommGrpCat.{u}).hom).app G := sorry

end AlgebraicGeometry.Scheme.Etale

end
