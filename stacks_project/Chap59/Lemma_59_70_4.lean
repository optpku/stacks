/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.OpenImmersion
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.70.4 (1): for an open immersion `j : U ⟶ X` and an abelian étale
sheaf `F` on `U`, the adjunction unit `F ⟶ j⁻¹ (j_! F)` is an isomorphism,
where `j_!` is `abelianExtensionByZero` and `j⁻¹` is `etaleRestrictionSheaf`. -/
@[stacks 0F70] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZero_unit_isIso_of_isOpenImmersion :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension F]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}),
      IsIso ((abelianExtensionByZero_adjunction j).unit.app F))

/- Lemma 59.70.4 (2): for an open immersion `j : U ⟶ X` and an abelian étale
sheaf `F` on `U`, the adjunction counit `j⁻¹ (j_* F) ⟶ F` is an isomorphism,
where `j_*` is the continuous sheaf pushforward of `smallEtalePullback j` and
`j⁻¹` is the matching sheaf pullback. -/
@[stacks 0F70] #check (AlgebraicGeometry.Scheme.abelianDirectImage_counit_isIso_of_isOpenImmersion :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      [((smallEtalePullback j).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}),
      IsIso (((smallEtalePullback j).sheafAdjunctionContinuous
        AddCommGrpCat.{u} X.smallEtaleTopology U.smallEtaleTopology).counit.app F))

/- Lemma 59.70.4 (3): `j_! F` is unique up to isomorphism among abelian étale
sheaves on `X` whose restriction to `U` is `F` and whose stalks vanish at
geometric points of `X` whose image misses `j.opensRange`. -/
@[stacks 0F70] #check (AlgebraicGeometry.Scheme.abelianExtensionByZero_unique_of_restriction_and_vanishingStalks :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension F]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (e : (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅ F)
      (hG : ∀ xbar : GeometricPoint X, xbar.image ∉ j.opensRange →
        IsZero ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj G)),
      Nonempty (G ≅ (abelianExtensionByZero j).obj F))

/- Lemma 59.70.4 (4): the stalks of `j_! F` vanish at geometric points
whose image is outside `j.opensRange`. -/
@[stacks 0F70] #check (AlgebraicGeometry.Scheme.abelianExtensionByZero_stalk_isZero_of_not_mem_opensRange :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension F]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
      (xbar : GeometricPoint X) (hx : xbar.image ∉ j.opensRange),
      IsZero ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
        ((abelianExtensionByZero j).obj F)))

end AlgebraicGeometry.Scheme
