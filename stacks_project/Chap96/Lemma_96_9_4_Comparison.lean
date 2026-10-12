/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite
public import stacks_project.Chap96.Lemma_96_9_1_Localizing

/-!
# Ringed comparison along `overPostScheme`

The site functor `overPostScheme p x : Over x ⥤ Over U` of Lemma 96.9.1 extends
to a morphism of ringed sites from `((Sch/U)_τ, 𝒪)` to the slice
`(𝒳_τ / x, 𝒪_𝒳|_x)`, by the identity on underlying schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Identity-on-schemes comparison from the realization of `overPostScheme p x`
to `Over.forget x ⋙ p ⋙ Over.forget S`. -/
def schemeProjection (𝒳 : GroupoidsOver S) (x : 𝒳.total) :
    overPostScheme 𝒳.p x ⋙ Over.forget (𝒳.p.obj x).left ⟶
      Over.forget x ⋙ 𝒳.p ⋙ Over.forget S where
  app _ := 𝟙 _
  naturality := sorry

/-- `schemeProjection` is objectwise the identity of the underlying scheme. -/
theorem schemeProjection_app (𝒳 : GroupoidsOver S) (x : 𝒳.total) (y : Over x) :
    (schemeProjection 𝒳 x).app y = 𝟙 _ :=
  sorry

/-- Reassociation identifying the slice of `𝒪_𝒳` at `x` with the global-sections
presheaf of `Over.forget x ⋙ 𝒳.p ⋙ Over.forget S`. -/
def localizationStructurePresheafIso (𝒳 : GroupoidsOver S) (τ : StandardTopology)
    (x : 𝒳.total) :
    ((associatedRingedSite 𝒳 τ).localization x).structureSheaf.obj ≅
      Scheme.Site.structurePresheaf (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S) :=
  isoWhiskerLeft (Over.forget x).op
      ((𝒳.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
          (𝒳.associatedTopology τ) (τ.overTopology S)).app
        (StandardTopology.Big.structureSheaf τ S)) ≪≫
    (associator (Over.forget x).op 𝒳.p.op
        (StandardTopology.Big.structureSheaf τ S).obj).symm ≪≫
    (associator ((Over.forget x).op ⋙ 𝒳.p.op) (Over.forget S).op
        (Scheme.Γ ⋙ forget₂ CommRingCat RingCat)).symm ≪≫
    isoWhiskerRight (associator (Over.forget x).op 𝒳.p.op (Over.forget S).op)
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat) ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (Over.forget x).op ((𝒳.p).opComp (Over.forget S)).symm)
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat) ≪≫
    isoWhiskerRight ((Over.forget x).opComp (𝒳.p ⋙ Over.forget S)).symm
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat)

/-- Objectwise, `localizationStructurePresheafIso` identifies sections of the
slice of `𝒪_𝒳` with global sections of the composite realization. -/
theorem localizationStructurePresheafIso_obj (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) (y : Over x) :
    ((associatedRingedSite 𝒳 τ).localization x).structureSheaf.obj.obj (op y) =
      (Scheme.Site.structurePresheaf
        (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S)).obj (op y) :=
  sorry

/-- `overPostScheme` is continuous from the localized associated `τ`-site of `𝒳`
at `x` to `(Sch/U)_τ`. -/
instance overPostScheme_isContinuous (𝒳 : GroupoidsOver S) (τ : StandardTopology)
    (x : 𝒳.total) :
    (overPostScheme 𝒳.p x).IsContinuous
      ((associatedRingedSite 𝒳 τ).localization x).siteTopology
      (τ.overTopology (𝒳.p.obj x).left) :=
  (overPostScheme.isMorphismOfSites 𝒳.p x τ).toIsContinuous

/-- The comparison `(𝒪_𝒳).over x ⟶ (overPostScheme p x)_* 𝒪_{(Sch/U)_τ}`
induced by global sections of `schemeProjection`, after reassociating the slice
sheaf to that composite's global-sections presheaf. -/
def overPostSchemeRingedSiteHom_structureSheafMap (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    ((associatedRingedSite 𝒳 τ).localization x).structureSheaf ⟶
      ((overPostScheme 𝒳.p x).sheafPushforwardContinuous RingCat.{u}
          ((associatedRingedSite 𝒳 τ).localization x).siteTopology
          (τ.overTopology (𝒳.p.obj x).left)).obj
        (StandardTopology.Big.structureSheaf τ (𝒳.p.obj x).left) :=
  { hom :=
      (localizationStructurePresheafIso 𝒳 τ x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S)
          (Over.forget (𝒳.p.obj x).left)
          (overPostScheme 𝒳.p x) (schemeProjection 𝒳 x) }

/-- `overPostSchemeRingedSiteHom_structureSheafMap` is the reassociating iso
followed by the global-sections map of `schemeProjection`. -/
theorem overPostSchemeRingedSiteHom_structureSheafMap_hom (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    (overPostSchemeRingedSiteHom_structureSheafMap 𝒳 τ x).hom =
      (localizationStructurePresheafIso 𝒳 τ x).hom ≫
        Scheme.Site.structurePresheafMap
          (Over.forget x ⋙ 𝒳.p ⋙ Over.forget S)
          (Over.forget (𝒳.p.obj x).left)
          (overPostScheme 𝒳.p x) (schemeProjection 𝒳 x) :=
  sorry

/-- The morphism of ringed sites from the localized associated `τ`-site of `𝒳`
at `x` to the big `τ`-site of `U = p(x)`, with base functor
`overPostScheme 𝒳.p x`. -/
def overPostSchemeRingedSiteHom (𝒳 : GroupoidsOver S) (τ : StandardTopology)
    (x : 𝒳.total) :
    RingedSite.Hom (StandardTopology.Big.ringedSite τ (𝒳.p.obj x).left)
      ((associatedRingedSite 𝒳 τ).localization x) where
  base := overPostScheme 𝒳.p x
  isMorphismOfSites := overPostScheme.isMorphismOfSites 𝒳.p x τ
  structureSheafMap := overPostSchemeRingedSiteHom_structureSheafMap 𝒳 τ x

/-- The base functor of `overPostSchemeRingedSiteHom` is `overPostScheme` of the
projection. -/
theorem overPostSchemeRingedSiteHom_base (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    (overPostSchemeRingedSiteHom 𝒳 τ x).base = overPostScheme 𝒳.p x :=
  sorry

/-- The structure-sheaf map of `overPostSchemeRingedSiteHom` is
`overPostSchemeRingedSiteHom_structureSheafMap`. -/
theorem overPostSchemeRingedSiteHom_structureSheafMap_eq (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) (x : 𝒳.total) :
    (overPostSchemeRingedSiteHom 𝒳 τ x).structureSheafMap =
      overPostSchemeRingedSiteHom_structureSheafMap 𝒳 τ x :=
  sorry

end AlgebraicGeometry.GroupoidsOver
