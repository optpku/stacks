module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction

/-!
# Section comparison of scheme-restriction presentations

Canonical native-chart restriction and the scheme-site/open-subscheme presentation
have the same actual chart sections. This leaf owns their two-way comparison,
identity restriction data, and section computation rules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}}

/-- Identity postcomposition on the small etale site, by actual identity maps
of the represented schemes. -/
def identitySiteIso (Z : Over S) :
    Modules.restrictPostcompose (𝟙 (ofOver Z)) ≅ 𝟭 (smallEtaleSite (ofOver Z)) :=
  NatIso.ofComponents (fun W ↦
    { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 W.left) trivial sorry
      inv := MorphismProperty.CostructuredArrow.homMk (𝟙 W.left) trivial sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }) sorry

/-- The identity-on-sections ring comparison is compatible with that site isomorphism. -/
theorem identityRingMap (Z : Over S) :
    Modules.restrictStructureMap (𝟙 (ofOver Z)) ≫
      (Functor.sheafPushforwardContinuousNatTrans (identitySiteIso Z).inv
        RingCat.{u} (smallEtaleTopology (ofOver Z)) (smallEtaleTopology (ofOver Z))).app
          (structureSheaf (ofOver Z)) = 𝟙 (structureSheaf (ofOver Z)) := sorry

/-- Restriction along the identity is canonically the identity on modules. -/
def identityRestrictionIso (Z : Over S) :
    Modules.restrictFunctor (𝟙 (ofOver Z)) ≅ 𝟭 (ofOver Z).Modules :=
  SheafOfModules.pushforwardCongr₂
      (φ := Modules.restrictStructureMap (𝟙 (ofOver Z)))
      (identitySiteIso Z).symm (identityRingMap Z) ≪≫
    SheafOfModules.pushforwardId (structureSheaf (ofOver Z))

/-- Continuity from the actual ringed-site morphism's stored site proof. -/
instance schemeBaseContinuous (Z : Over S) :
    (schemeEtaleRingedHom Z).base.IsContinuous
      (Scheme.Etale.Small.ringedSite Z.left).siteTopology
      (ringedSite (ofOver Z)).siteTopology :=
  (schemeEtaleRingedHom Z).isMorphismOfSites.toIsContinuous

/-- Continuity of the open-to-etale base functor, from its stored proof. -/
instance opensBaseContinuous (Y : Scheme.{u}) :
    (smallEtaleToOpensRingedHom Y).base.IsContinuous
      (Opens.grothendieckTopology Y) (Scheme.Etale.Small.ringedSite Y).siteTopology :=
  (smallEtaleToOpensRingedHom Y).isMorphismOfSites.toIsContinuous

/-- The precise small-etale object at which restriction evaluates an open. -/
def siteObject (Z : Over S) (V : Z.left.Opens) : smallEtaleSite (ofOver Z) :=
  (Modules.restrictPostcompose (𝟙 (ofOver Z))).obj
    ((schemeEtaleRingedHom Z).base.obj
      ((smallEtaleToOpensRingedHom Z.left).base.obj V))

/-- Restriction does not change the underlying section values at that object. -/
def sectionEquiv (Z : Over S) (M : (ofOver Z).Modules) (V : Z.left.Opens) :
    ((Modules.restrictToScheme Z).obj M).val.obj (op V) ≃
      M.val.obj (op (siteObject Z V)) := by
  dsimp only [Modules.restrictToScheme, Functor.comp_obj, RingedSite.Hom.modulePushforward,
    opensToSchemeModules, SheafOfModules.pushforward, SheafOfModules.restrictScalars,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj, Modules.restrictFunctor, siteObject]
  exact Equiv.refl _

/-- The direct-image composite before the harmless identity restriction. -/
def restrictionBare (Z : Over S) : (ofOver Z).Modules ⥤ Z.left.Modules :=
  (schemeEtaleRingedHom Z).modulePushforward.{u} ⋙
    (smallEtaleToOpensRingedHom Z.left).modulePushforward.{u} ⋙
      opensToSchemeModules Z.left

/-- The scheme-site presentation evaluates a module at its actual open chart. -/
def bareSectionEquiv (Z : Over S) (M : (ofOver Z).Modules) (V : Z.left.Opens) :
    ((restrictionBare Z).obj M).val.obj (op V) ≃
      M.val.obj (op (siteObject Z V)) := by
  dsimp only [restrictionBare, Functor.comp_obj, RingedSite.Hom.modulePushforward,
    opensToSchemeModules, SheafOfModules.pushforward, SheafOfModules.restrictScalars,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj, siteObject]
  exact Equiv.refl _

/-- Compare native-chart restriction with the scheme-site presentation by identity section maps. -/
def restrictionIsoBare (Z : Over S) : Modules.restrictToScheme Z ≅ restrictionBare Z :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          { val :=
              { app := fun V ↦ by
                  let A := ((Modules.restrictToScheme Z).obj M).val.obj V
                  let B := ((restrictionBare Z).obj M).val.obj V
                  exact @ModuleCat.ofHom (Z.left.ringCatSheaf.obj.obj V) _ A B
                    A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
                    { toFun := fun x ↦ (bareSectionEquiv Z M V.unop).symm
                        (sectionEquiv Z M V.unop x)
                      map_add' := sorry
                      map_smul' := sorry }
                naturality := sorry } }
        inv :=
          { val :=
              { app := fun V ↦ by
                  let A := ((Modules.restrictToScheme Z).obj M).val.obj V
                  let B := ((restrictionBare Z).obj M).val.obj V
                  exact @ModuleCat.ofHom (Z.left.ringCatSheaf.obj.obj V) _ B A
                    B.isAddCommGroup B.isModule A.isAddCommGroup A.isModule
                    { toFun := fun x ↦ (sectionEquiv Z M V.unop).symm
                        (bareSectionEquiv Z M V.unop x)
                      map_add' := sorry
                      map_smul' := sorry }
                naturality := sorry } }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The forward comparison keeps the actual section under the two chart presentations. -/
@[simp]
theorem restrictionIsoBare_hom_app_apply (Z : Over S) (M : (ofOver Z).Modules)
    (V : Z.left.Opens) (x : ((Modules.restrictToScheme Z).obj M).val.obj (op V)) :
    (((restrictionIsoBare Z).hom.app M).val.app (op V)).hom x =
      (bareSectionEquiv Z M V).symm (sectionEquiv Z M V x) := rfl

/-- The reverse comparison keeps the same actual section. -/
@[simp]
theorem restrictionIsoBare_inv_app_apply (Z : Over S) (M : (ofOver Z).Modules)
    (V : Z.left.Opens) (x : ((restrictionBare Z).obj M).val.obj (op V)) :
    (((restrictionIsoBare Z).inv.app M).val.app (op V)).hom x =
      (sectionEquiv Z M V).symm (bareSectionEquiv Z M V x) := rfl

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
