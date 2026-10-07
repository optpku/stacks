module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_18_3

/-!
# Comparison of small étale and Zariski quasi-coherent modules on a scheme

A scheme `U` over `S`, viewed as an algebraic space, has small étale quasi-coherent modules
canonically comparable with Zariski quasi-coherent modules on the underlying scheme `U.left`.
The comparison is the composite of étale restriction, the site morphism from `ofOver U` to
the small étale site of `U.left`, and the Zariski identification of étale modules with
`Scheme.Modules`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale morphism of schemes over `S` remains étale after viewing it as a morphism of
algebraic spaces via `ofOverMap`. -/
instance etale_ofOverMap_of_etale {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Etale h.left] : Etale (ofOverMap h) :=
  sorry

/-- The scheme over `S` underlying an object of the small étale site of `U`. -/
def schemeEtaleOverObj {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) : Over S :=
  Over.mk (W.hom ≫ U.hom)

/-- The structure morphism of `schemeEtaleOverObj U W` is `W.hom ≫ U.hom`. -/
theorem schemeEtaleOverObj_hom {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    (schemeEtaleOverObj U W).hom = W.hom ≫ U.hom :=
  rfl

/-- The morphism `ofOver (schemeEtaleOverObj U W) ⟶ ofOver U` induced by `W.hom`. -/
def schemeEtaleOverHom {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    schemeEtaleOverObj U W ⟶ U :=
  Over.homMk W.hom rfl

/-- The underlying scheme morphism of `schemeEtaleOverHom U W` is `W.hom`. -/
theorem schemeEtaleOverHom_left {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    (schemeEtaleOverHom U W).left = W.hom :=
  rfl

/-- The structure morphism of `schemeEtaleOverHom U W` is étale as a morphism of schemes. -/
instance etale_schemeEtaleOverHom_left {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    AlgebraicGeometry.Etale (schemeEtaleOverHom U W).left :=
  W.prop

/-- The algebraic-space morphism `ofOverMap (schemeEtaleOverHom U W)` is étale. -/
instance etale_ofOverMap_schemeEtaleOverHom {S : Scheme.{u}} (U : Over S)
    (W : U.left.Etale) : Etale (ofOverMap (schemeEtaleOverHom U W)) :=
  etale_ofOverMap_of_etale (schemeEtaleOverHom U W)

/-- The object of the small étale site of `ofOver U` associated to a scheme étale over `U`. -/
def schemeEtaleToSmallEtaleObj {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    smallEtaleSite (ofOver U) :=
  smallEtaleSite.mk (ofOverMap (schemeEtaleOverHom U W))

/-- On objects, `schemeEtaleToSmallEtaleObj U W` is `smallEtaleSite.mk` of `ofOverMap` of
`schemeEtaleOverHom U W`. -/
theorem schemeEtaleToSmallEtaleObj_eq {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    schemeEtaleToSmallEtaleObj U W =
      smallEtaleSite.mk (ofOverMap (schemeEtaleOverHom U W)) :=
  rfl

/-- The morphism in `Over S` induced by a morphism of schemes étale over `U`. -/
def schemeEtaleOverMap {S : Scheme.{u}} (U : Over S) {W W' : U.left.Etale} (f : W ⟶ W') :
    schemeEtaleOverObj U W ⟶ schemeEtaleOverObj U W' :=
  Over.homMk f.left sorry

/-- The underlying scheme morphism of `schemeEtaleOverMap U f` is `f.left`. -/
theorem schemeEtaleOverMap_left {S : Scheme.{u}} (U : Over S) {W W' : U.left.Etale}
    (f : W ⟶ W') : (schemeEtaleOverMap U f).left = f.left :=
  rfl

/-- The functor from the small étale site of a scheme `U` over `S` to the small étale site of
the associated algebraic space `ofOver U`. -/
def schemeEtaleToSmallEtale {S : Scheme.{u}} (U : Over S) :
    U.left.Etale ⥤ smallEtaleSite (ofOver U) where
  obj := schemeEtaleToSmallEtaleObj U
  map {W W'} f :=
    MorphismProperty.CostructuredArrow.homMk (schemeEtaleOverMap U f) trivial sorry
  map_id := sorry
  map_comp := sorry

/-- The object map of `schemeEtaleToSmallEtale` is `schemeEtaleToSmallEtaleObj`. -/
@[simp]
theorem schemeEtaleToSmallEtale_obj {S : Scheme.{u}} (U : Over S) (W : U.left.Etale) :
    (schemeEtaleToSmallEtale U).obj W = schemeEtaleToSmallEtaleObj U W :=
  rfl

/-- The comparison from schemes étale over `U` to the small étale site of `ofOver U` is a
morphism of sites. -/
instance schemeEtaleToSmallEtale_isMorphismOfSites {S : Scheme.{u}} (U : Over S) :
    IsMorphismOfSites U.left.smallEtaleTopology (smallEtaleTopology (ofOver U))
      (schemeEtaleToSmallEtale U) :=
  sorry

/-- Realization of `schemeEtaleToSmallEtale` as schemes recovers the source-scheme functor of
the small étale site of `U`. -/
def schemeEtaleToSmallEtale_schemeProjection {S : Scheme.{u}} (U : Over S) :
    schemeEtaleToSmallEtale U ⋙ smallEtaleToScheme (ofOver U) ⟶
      Scheme.smallEtaleToScheme U.left where
  app W := 𝟙 _
  naturality := sorry

/-- Components of `schemeEtaleToSmallEtale_schemeProjection` are identity morphisms. -/
theorem schemeEtaleToSmallEtale_schemeProjection_app {S : Scheme.{u}} (U : Over S)
    (W : U.left.Etale) :
    (schemeEtaleToSmallEtale_schemeProjection U).app W = 𝟙 _ :=
  rfl

/-- The ringed-site morphism from the small étale ringed site of `ofOver U` to the small étale
ringed site of the underlying scheme of `U`. -/
def schemeEtaleRingedHom {S : Scheme.{u}} (U : Over S) :
    RingedSite.Hom (ringedSite (ofOver U)) (Scheme.Etale.Small.ringedSite U.left) :=
  Scheme.Site.ringedHom U.left.smallEtaleTopology (smallEtaleTopology (ofOver U))
    (Scheme.smallEtaleToScheme U.left) (smallEtaleToScheme (ofOver U))
    (schemeEtaleToSmallEtale U) (schemeEtaleToSmallEtale_schemeProjection U)
    (Scheme.Etale.Small.structurePresheaf_isSheaf U.left)
    (structurePresheaf_isSheaf (ofOver U))

/-- The base of `schemeEtaleRingedHom U` is `schemeEtaleToSmallEtale U`. -/
theorem schemeEtaleRingedHom_base {S : Scheme.{u}} (U : Over S) :
    (schemeEtaleRingedHom U).base = schemeEtaleToSmallEtale U :=
  sorry

/-- The composite inclusion of open immersions among étale morphisms is a morphism of sites. -/
instance smallZariskiOpenToSmallEtale_isMorphismOfSites (S : Scheme.{u}) :
    IsMorphismOfSites (Opens.grothendieckTopology (S : TopCat)) S.smallEtaleTopology
      (Scheme.smallZariskiOpenFunctor S ⋙
        Scheme.SiteRestriction.smallZariskiToSmallEtale S) :=
  sorry

/-- Global sections of open subschemes of `S` form a sheaf on the usual open-cover topology. -/
theorem opensStructurePresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (S : TopCat))
      (Scheme.Site.structurePresheaf (S.restrictFunctor ⋙ Over.forget S)) :=
  sorry

/-- Realization of open immersions as étale schemes recovers the open-subscheme functor. -/
def smallZariskiOpenToSmallEtale_schemeProjection (S : Scheme.{u}) :
    (Scheme.smallZariskiOpenFunctor S ⋙
        Scheme.SiteRestriction.smallZariskiToSmallEtale S) ⋙
      Scheme.smallEtaleToScheme S ⟶
        S.restrictFunctor ⋙ Over.forget S where
  app U := 𝟙 _
  naturality := sorry

/-- Components of `smallZariskiOpenToSmallEtale_schemeProjection` are identity morphisms. -/
theorem smallZariskiOpenToSmallEtale_schemeProjection_app (S : Scheme.{u}) (U : S.Opens) :
    (smallZariskiOpenToSmallEtale_schemeProjection S).app U = 𝟙 _ :=
  rfl

/-- The ringed-site morphism from the small étale ringed site of a scheme to the ringed site of
open subschemes with values `Γ(U, 𝒪_U)`. -/
def smallEtaleToOpensRingedHom (S : Scheme.{u}) :
    RingedSite.Hom (Scheme.Etale.Small.ringedSite S)
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (S : TopCat))
        ⟨Scheme.Site.structurePresheaf (S.restrictFunctor ⋙ Over.forget S),
          opensStructurePresheaf_isSheaf S⟩) :=
  Scheme.Site.ringedHom (Opens.grothendieckTopology (S : TopCat)) S.smallEtaleTopology
    (S.restrictFunctor ⋙ Over.forget S) (Scheme.smallEtaleToScheme S)
    (Scheme.smallZariskiOpenFunctor S ⋙ Scheme.SiteRestriction.smallZariskiToSmallEtale S)
    (smallZariskiOpenToSmallEtale_schemeProjection S)
    (opensStructurePresheaf_isSheaf S)
    (Scheme.Etale.Small.structurePresheaf_isSheaf S)

/-- The base of `smallEtaleToOpensRingedHom S` is the composite of the open-immersion functor
with the small Zariski-to-étale comparison. -/
theorem smallEtaleToOpensRingedHom_base (S : Scheme.{u}) :
    (smallEtaleToOpensRingedHom S).base =
      Scheme.smallZariskiOpenFunctor S ⋙
        Scheme.SiteRestriction.smallZariskiToSmallEtale S :=
  sorry

/-- Restriction of scalars along the inverse of `Scheme.restrictFunctorΓ`, as a morphism of
ring sheaves. -/
def opensStructureToRingCatSheaf (S : Scheme.{u}) :
    S.ringCatSheaf ⟶
      ⟨Scheme.Site.structurePresheaf (S.restrictFunctor ⋙ Over.forget S),
        opensStructurePresheaf_isSheaf S⟩ :=
  ⟨Functor.whiskerRight (@Scheme.restrictFunctorΓ S).inv (forget₂ CommRingCat RingCat)⟩

/-- The underlying presheaf map of `opensStructureToRingCatSheaf` is whiskering of
`Scheme.restrictFunctorΓ.inv` with the forgetful functor to `RingCat`. -/
theorem opensStructureToRingCatSheaf_hom (S : Scheme.{u}) :
    (opensStructureToRingCatSheaf S).hom =
      Functor.whiskerRight (@Scheme.restrictFunctorΓ S).inv (forget₂ CommRingCat RingCat) :=
  rfl

/-- Transport of module sheaves from the open-subscheme global-sections presentation to
`Scheme.Modules`. -/
def opensToSchemeModules (S : Scheme.{u}) :
    RingedSite.ModuleCat.{u}
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (S : TopCat))
        ⟨Scheme.Site.structurePresheaf (S.restrictFunctor ⋙ Over.forget S),
          opensStructurePresheaf_isSheaf S⟩) ⥤
      S.Modules :=
  SheafOfModules.restrictScalars (opensStructureToRingCatSheaf S)

/-- `opensToSchemeModules` is restriction of scalars along `opensStructureToRingCatSheaf`. -/
theorem opensToSchemeModules_eq (S : Scheme.{u}) :
    opensToSchemeModules S =
      SheafOfModules.restrictScalars (opensStructureToRingCatSheaf S) :=
  rfl

namespace Modules

/-- Restriction of an `𝒪_{ofOver U}`-module to the underlying scheme of `U`. -/
def restrictToScheme {S : Scheme.{u}} (U : Over S) :
    (ofOver U).Modules ⥤ U.left.Modules :=
  restrictFunctor (𝟙 (ofOver U)) ⋙
    (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
      (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ⋙
        opensToSchemeModules U.left

/-- Objectwise, `restrictToScheme U` is identity restriction followed by the scheme-module
comparison. -/
theorem restrictToScheme_obj {S : Scheme.{u}} (U : Over S) (F : (ofOver U).Modules) :
    (restrictToScheme U).obj F =
      (opensToSchemeModules U.left).obj
        ((smallEtaleToOpensRingedHom U.left).modulePushforward.{u}.obj
          ((schemeEtaleRingedHom U).modulePushforward.{u}.obj
            ((restrictFunctor (𝟙 (ofOver U))).obj F))) :=
  rfl

/-- `restrictToScheme` is the displayed composite of étale restriction with the two ringed-site
module pushforwards and the open-to-scheme comparison. -/
theorem restrictToScheme_spec {S : Scheme.{u}} (U : Over S) :
    restrictToScheme U =
      restrictFunctor (𝟙 (ofOver U)) ⋙
        (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
          (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ⋙
            opensToSchemeModules U.left :=
  rfl

end Modules

namespace QCoh

/-- Restriction of quasi-coherent modules from `ofOver U` to Zariski quasi-coherent modules on
the underlying scheme of `U`. -/
def restrictToScheme {S : Scheme.{u}} (U : Over S) :
    QCoh (ofOver U) ⥤ Scheme.QCoh U.left :=
  FullSubcategory.restrict (Modules.restrictToScheme U) sorry

/-- The underlying module of `restrictToScheme U` is the module-level comparison composite. -/
theorem restrictToScheme_obj {S : Scheme.{u}} (U : Over S) (F : QCoh (ofOver U)) :
    ((restrictToScheme U).obj F).obj = (Modules.restrictToScheme U).obj F.obj :=
  sorry

end QCoh

end AlgebraicGeometry.AlgebraicSpace
