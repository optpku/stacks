/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_105_1_Triangle

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe w u

namespace AlgebraicGeometry.IsBlowup.Etale

variable {X X' : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (p : A ⟶ B),
    (abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]
variable [∀ {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C),
    (abelianPushforwardAlong f ⋙ abelianPushforwardAlong g).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]

/-- Canonical identification `(K|_{X'})|_E ≅ (K|_Z)|_E` of the two iterated inverse images
along the blow-up square. -/
noncomputable def exceptionalRestrictIso (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    (etaleDerivedInverseImage (I.comap b).subschemeι).obj
        ((etaleDerivedInverseImage b).obj K) ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj
        ((etaleDerivedInverseImage I.subschemeι).obj K) :=
  (inverseImageCompIso b (I.comap b).subschemeι).app K ≪≫
    (composite_inverseImageIso I b).app K ≪≫
    (inverseImageCompIso I.subschemeι (exceptionalProjection I b)).symm.app K

/-- `exceptionalRestrictIso` is inverse-image composition on the blow-up, transport along the
two composites, and the inverse composition comparison on the center. -/
theorem exceptionalRestrictIso_eq (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    exceptionalRestrictIso I b K =
      (inverseImageCompIso b (I.comap b).subschemeι).app K ≪≫
        (composite_inverseImageIso I b).app K ≪≫
        (inverseImageCompIso I.subschemeι (exceptionalProjection I b)).symm.app K :=
  sorry

/-- Compatibility `γ = g|_E ∘ f⁻¹|_E` of glueing isomorphisms on the exceptional divisor,
rewritten without inverses as `j⁻¹ f ≫ γ = exceptionalRestrictIso ≫ π⁻¹ g`. -/
def IsCompatibleOnExceptional (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    {K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})}
    {L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})}
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})}
    (f : (etaleDerivedInverseImage b).obj K ≅ K')
    (g : (etaleDerivedInverseImage I.subschemeι).obj K ≅ L) : Prop :=
  (etaleDerivedInverseImage (I.comap b).subschemeι).map f.hom ≫ γ.hom =
    (exceptionalRestrictIso I b K).hom ≫
      (etaleDerivedInverseImage (exceptionalProjection I b)).map g.hom

/-- Unfold `IsCompatibleOnExceptional` as equality of the two paths `j⁻¹ (b⁻¹ K) ⟶ π⁻¹ L`. -/
theorem isCompatibleOnExceptional_iff (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    {K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})}
    {L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})}
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})}
    (f : (etaleDerivedInverseImage b).obj K ≅ K')
    (g : (etaleDerivedInverseImage I.subschemeι).obj K ≅ L) :
    IsCompatibleOnExceptional I b γ f g ↔
      (etaleDerivedInverseImage (I.comap b).subschemeι).map f.hom ≫ γ.hom =
        (exceptionalRestrictIso I b K).hom ≫
          (etaleDerivedInverseImage (exceptionalProjection I b)).map g.hom :=
  sorry

/-- Compatibility `α|_E = β|_E ∘ γ` of a pair of restrictions, after transporting
`(M|_{X'})|_E ≅ (M|_Z)|_E` by `exceptionalRestrictIso`. -/
def IsCompatibleRestrictions (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    {K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})}
    {L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})}
    {M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})}
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L)
    (α : K' ⟶ (etaleDerivedInverseImage b).obj M)
    (β : L ⟶ (etaleDerivedInverseImage I.subschemeι).obj M) : Prop :=
  (etaleDerivedInverseImage (I.comap b).subschemeι).map α ≫
      (exceptionalRestrictIso I b M).hom =
    γ.hom ≫ (etaleDerivedInverseImage (exceptionalProjection I b)).map β

/-- Unfold `IsCompatibleRestrictions` as equality of the two paths `K'|_E ⟶ (M|_Z)|_E`. -/
theorem isCompatibleRestrictions_iff (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    {K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})}
    {L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})}
    {M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})}
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L)
    (α : K' ⟶ (etaleDerivedInverseImage b).obj M)
    (β : L ⟶ (etaleDerivedInverseImage I.subschemeι).obj M) :
    IsCompatibleRestrictions I b γ α β ↔
      (etaleDerivedInverseImage (I.comap b).subschemeι).map α ≫
          (exceptionalRestrictIso I b M).hom =
        γ.hom ≫ (etaleDerivedInverseImage (exceptionalProjection I b)).map β :=
  sorry

/-- The adjunction comparison `Ri_*(L) ⟶ Rc_*(L|_E)` along the center of a blow-up square. -/
noncomputable def pushforwardToExceptional_center (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I]
    (L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward I.subschemeι).obj L) ⟶
      DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward (composite I b)).obj
          ((etaleDerivedInverseImage (exceptionalProjection I b)).obj L)) :=
  DerivedCategory.Plus.ι.map
    ((etaleDerivedPushforward I.subschemeι).map
        (unitApp (exceptionalProjection I b) L) ≫
      (asIso (pushforwardCompComparison (exceptionalProjection I b) I.subschemeι)).inv.app
        ((etaleDerivedInverseImage (exceptionalProjection I b)).obj L))

/-- `pushforwardToExceptional_center` is derived pushforward of the exceptional-projection
unit, followed by the inverse composition comparison. -/
theorem pushforwardToExceptional_center_def (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I]
    (L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})) :
    pushforwardToExceptional_center I b L =
      DerivedCategory.Plus.ι.map
        ((etaleDerivedPushforward I.subschemeι).map
            (unitApp (exceptionalProjection I b) L) ≫
          (asIso (pushforwardCompComparison (exceptionalProjection I b) I.subschemeι)).inv.app
            ((etaleDerivedInverseImage (exceptionalProjection I b)).obj L)) :=
  sorry

/-- The adjunction comparison `Rb_*(K') ⟶ Rc_*(K'|_E)` along the blow-up of a blow-up square. -/
noncomputable def pushforwardToExceptional_blowup (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I]
    (K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward b).obj K') ⟶
      DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward (composite I b)).obj
          ((etaleDerivedInverseImage (I.comap b).subschemeι).obj K')) :=
  DerivedCategory.Plus.ι.map
    ((etaleDerivedPushforward b).map (unitApp (I.comap b).subschemeι K') ≫
      (asIso (pushforwardCompComparison (I.comap b).subschemeι b)).inv.app
        ((etaleDerivedInverseImage (I.comap b).subschemeι).obj K') ≫
      (composite_pushforwardIso I b).hom.app
        ((etaleDerivedInverseImage (I.comap b).subschemeι).obj K'))

/-- `pushforwardToExceptional_blowup` is derived pushforward of the exceptional-immersion
unit, followed by the inverse composition comparison and transport along the two composites. -/
theorem pushforwardToExceptional_blowup_def (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I]
    (K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})) :
    pushforwardToExceptional_blowup I b K' =
      DerivedCategory.Plus.ι.map
        ((etaleDerivedPushforward b).map (unitApp (I.comap b).subschemeι K') ≫
          (asIso (pushforwardCompComparison (I.comap b).subschemeι b)).inv.app
            ((etaleDerivedInverseImage (I.comap b).subschemeι).obj K') ≫
          (composite_pushforwardIso I b).hom.app
            ((etaleDerivedInverseImage (I.comap b).subschemeι).obj K')) :=
  sorry

/-- The signed glueing map `Ri_*(L) ⊞ Rb_*(K') ⟶ Rc_*(L|_E)` whose cone is a glued object. -/
noncomputable def glueComparison (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))
    (L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u}))
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L) :
    DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward I.subschemeι).obj L) ⊞
      DerivedCategory.Plus.ι.obj ((etaleDerivedPushforward b).obj K') ⟶
      DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward (composite I b)).obj
          ((etaleDerivedInverseImage (exceptionalProjection I b)).obj L)) :=
  biprod.desc (pushforwardToExceptional_center I b L)
    (-(pushforwardToExceptional_blowup I b K' ≫
      DerivedCategory.Plus.ι.map ((etaleDerivedPushforward (composite I b)).map γ.hom)))

/-- `glueComparison` is the signed biproduct descent of the center comparison and the blow-up
comparison postcomposed with `Rc_*(γ)`. -/
theorem glueComparison_def (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))
    (L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u}))
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L) :
    glueComparison I b K' L γ =
      biprod.desc (pushforwardToExceptional_center I b L)
        (-(pushforwardToExceptional_blowup I b K' ≫
          DerivedCategory.Plus.ι.map
            ((etaleDerivedPushforward (composite I b)).map γ.hom))) :=
  sorry

end AlgebraicGeometry.IsBlowup.Etale

end

end
