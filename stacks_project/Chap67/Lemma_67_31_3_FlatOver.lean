/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Relative flatness of quasi-coherent modules on algebraic spaces

A quasi-coherent module on an algebraic space is flat at a point over the target when some
étale scheme presentation reduces the condition to `Scheme.Modules.flatOverAt`. Restriction
along an étale scheme object is the composite of étale module restriction with the comparison
from the small étale ringed site of `ofOver U` to modules on the underlying scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

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

/-- Restriction of scalars along the inverse of `Scheme.restrictFunctorΓ`, as a morphism of
ring sheaves. -/
def opensStructureToRingCatSheaf (S : Scheme.{u}) :
    S.ringCatSheaf ⟶
      ⟨Scheme.Site.structurePresheaf (S.restrictFunctor ⋙ Over.forget S),
        opensStructurePresheaf_isSheaf S⟩ :=
  ⟨Functor.whiskerRight (@Scheme.restrictFunctorΓ S).inv (forget₂ CommRingCat RingCat)⟩

/-- Transport of module sheaves from the open-subscheme global-sections presentation to
`Scheme.Modules`. -/
def opensToSchemeModules (S : Scheme.{u}) :
    RingedSite.ModuleCat.{u}
      (RingedSite.ofRingSheaf (Opens.grothendieckTopology (S : TopCat))
        ⟨Scheme.Site.structurePresheaf (S.restrictFunctor ⋙ Over.forget S),
          opensStructurePresheaf_isSheaf S⟩) ⥤
      S.Modules :=
  SheafOfModules.restrictScalars (opensStructureToRingCatSheaf S)

namespace Modules

/-- The structural morphism of an object of the small étale site is étale. -/
instance etale_smallEtaleSite_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) : Etale U.hom :=
  U.prop

/-- Restriction of an `𝒪_X`-module along an étale scheme object `U → X`, viewed as a module
sheaf on the underlying scheme of `U`. -/
def restrictToScheme {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    X.Modules ⥤ U.left.left.Modules :=
  @restrictFunctor S (ofOver U.left) X U.hom U.prop ⋙
    (schemeEtaleRingedHom U.left).modulePushforward.{u} ⋙
      (smallEtaleToOpensRingedHom U.left.left).modulePushforward.{u} ⋙
        opensToSchemeModules U.left.left

/-- Objectwise, `restrictToScheme U` is étale restriction followed by the scheme-module
comparison. -/
theorem restrictToScheme_obj {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X)
    (F : X.Modules) :
    (restrictToScheme U).obj F =
      (opensToSchemeModules U.left.left).obj
        ((smallEtaleToOpensRingedHom U.left.left).modulePushforward.{u}.obj
          ((schemeEtaleRingedHom U.left).modulePushforward.{u}.obj
            ((restrictFunctor U.hom).obj F))) :=
  sorry

/-- `restrictToScheme` is the displayed composite of étale restriction with the two ringed-site
module pushforwards and the open-to-scheme comparison. -/
theorem restrictToScheme_spec {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    restrictToScheme U =
      restrictFunctor U.hom ⋙
        (schemeEtaleRingedHom U.left).modulePushforward.{u} ⋙
          (smallEtaleToOpensRingedHom U.left.left).modulePushforward.{u} ⋙
            opensToSchemeModules U.left.left :=
  sorry

/-- A quasi-coherent module `F` on `X` is flat at a point `x` over `Y` if some étale scheme
square over `f` has `a^* F` flat at a germ of `U` mapping to `x`. -/
def flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (sq : EtaleSquare f) (u : sq.left.left.left),
    Points.map sq.left.hom (ofOver.pointsEquiv sq.left.left u) = x ∧
      Scheme.Modules.flatOverAt ((restrictToScheme sq.left).obj F) sq.map.left u

/-- Pointwise relative flatness unpacks as the existence of an étale scheme presentation whose
restricted module is relatively flat at a germ mapping to the given point. -/
theorem flatOverAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    (x : Points X) :
    flatOverAt F f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
        (ha : Etale a) (hb : Etale b),
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Modules.flatOverAt
              ((restrictToScheme (smallEtaleSite.mk a)).obj F) h.left u :=
  sorry

/-- A quasi-coherent module on `X` is flat over `Y` if it is flat at every point of `X`. -/
def flatOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y) : Prop :=
  ∀ x : Points X, flatOverAt F f x

/-- Global relative flatness is the pointwise condition at every point of the source. -/
theorem flatOver_iff_forall_flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) :
    flatOver F f ↔ ∀ x : Points X, flatOverAt F f x :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
