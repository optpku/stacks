module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Category.TopCat.OpenNhds
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Neighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk

/-!
# Zariski stalks of pulled-back modules on scheme étale neighbourhoods

A scheme étale neighbourhood of a geometric point of an algebraic space identifies the
étale module stalk `F_{xbar}` with the tensor product of the Zariski stalk of `φ* F` against
the étale local ring `𝒪_{X, xbar}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood
open AlgebraicGeometry.Scheme.SiteRestriction
open TopologicalSpace ModuleCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricPoint.SmallEtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}

/-- A scheme-étale morphism commutes with the induced structure maps to the base scheme. -/
theorem ofSchemeEtaleMap_over_w (N : SmallEtaleNeighborhood xbar)
    {W W' : N.scheme.Etale} (f : W ⟶ W') :
    f.left ≫ (W'.hom ≫ N.toSite.left.hom) = W.hom ≫ N.toSite.left.hom :=
  sorry

/-- A scheme-étale morphism commutes with the induced structural arrows to the algebraic space. -/
theorem ofSchemeEtaleMap_w (N : SmallEtaleNeighborhood xbar)
    {W W' : N.scheme.Etale} (f : W ⟶ W') :
    (ofOverFunctor S).map
        (Over.homMk f.left (ofSchemeEtaleMap_over_w N f) :
          (ofSchemeEtale N W).left ⟶ (ofSchemeEtale N W').left) ≫
      (ofSchemeEtale N W').hom = (ofSchemeEtale N W).hom :=
  sorry

/-- The morphism of algebraic-space étale charts induced by a scheme-étale morphism. -/
def ofSchemeEtaleMap (N : SmallEtaleNeighborhood xbar)
    {W W' : N.scheme.Etale} (f : W ⟶ W') :
    ofSchemeEtale N W ⟶ ofSchemeEtale N W' :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk f.left (ofSchemeEtaleMap_over_w N f)) trivial (ofSchemeEtaleMap_w N f)

/-- The chart morphism induced by an identity scheme-étale morphism is the identity. -/
theorem ofSchemeEtaleMap_id (N : SmallEtaleNeighborhood xbar) (W : N.scheme.Etale) :
    ofSchemeEtaleMap N (𝟙 W) = 𝟙 (ofSchemeEtale N W) :=
  sorry

/-- Postcomposition of scheme-étale objects preserves composition of morphisms. -/
theorem ofSchemeEtaleMap_comp (N : SmallEtaleNeighborhood xbar)
    {W W' W'' : N.scheme.Etale} (f : W ⟶ W') (g : W' ⟶ W'') :
    ofSchemeEtaleMap N (f ≫ g) = ofSchemeEtaleMap N f ≫ ofSchemeEtaleMap N g :=
  sorry

/-- Postcomposition sends schemes étale over a neighbourhood to étale charts of the algebraic
space. -/
def ofSchemeEtaleFunctor (N : SmallEtaleNeighborhood xbar) :
    N.scheme.Etale ⥤ smallEtaleSite X where
  obj W := ofSchemeEtale N W
  map f := ofSchemeEtaleMap N f
  map_id W := ofSchemeEtaleMap_id N W
  map_comp f g := ofSchemeEtaleMap_comp N f g

/-- The object map of `ofSchemeEtaleFunctor` is `ofSchemeEtale`. -/
theorem ofSchemeEtaleFunctor_obj (N : SmallEtaleNeighborhood xbar) (W : N.scheme.Etale) :
    (ofSchemeEtaleFunctor N).obj W = ofSchemeEtale N W :=
  sorry

/-- Inclusion of Zariski opens of the neighbourhood scheme into the small étale site of `X`. -/
def zariskiOpenToEtale (N : SmallEtaleNeighborhood xbar) :
    N.scheme.Opens ⥤ smallEtaleSite X :=
  Scheme.smallZariskiOpenFunctor N.scheme ⋙
    smallZariskiToSmallEtale N.scheme ⋙ ofSchemeEtaleFunctor N

/-- `zariskiOpenToEtale` is the composite of the Zariski-to-étale inclusion with
`ofSchemeEtaleFunctor`. -/
theorem zariskiOpenToEtale_eq (N : SmallEtaleNeighborhood xbar) :
    zariskiOpenToEtale N =
      Scheme.smallZariskiOpenFunctor N.scheme ⋙
        smallZariskiToSmallEtale N.scheme ⋙ ofSchemeEtaleFunctor N :=
  sorry

/-- The inclusion of neighbourhood Zariski opens into the algebraic-space étale site is
continuous. -/
instance zariskiOpenToEtale_isContinuous (N : SmallEtaleNeighborhood xbar) :
    (zariskiOpenToEtale N).IsContinuous (Opens.grothendieckTopology N.scheme)
      (smallEtaleTopology X) :=
  sorry

/-- Realization comparison of a Zariski open, viewed as an étale neighbourhood object. -/
def zariskiOpen_schemeHom (N : SmallEtaleNeighborhood xbar) (U : N.scheme.Opens) :
    (smallEtaleToScheme X).obj ((zariskiOpenToEtale N).obj U) ⟶ U.toScheme :=
  ofSchemeEtale_schemeHom N
    ((smallZariskiToSmallEtale N.scheme).obj
      ((Scheme.smallZariskiOpenFunctor N.scheme).obj U))

/-- `zariskiOpen_schemeHom` is the identity comparison of the underlying open subscheme. -/
theorem zariskiOpen_schemeHom_eq (N : SmallEtaleNeighborhood xbar) (U : N.scheme.Opens) :
    zariskiOpen_schemeHom N U =
      ofSchemeEtale_schemeHom N
        ((smallZariskiToSmallEtale N.scheme).obj
          ((Scheme.smallZariskiOpenFunctor N.scheme).obj U)) :=
  sorry

/-- Canonical comparison of structure sheaves along `zariskiOpenToEtale`, given on sections by
restriction along `zariskiOpen_schemeHom`. -/
def toZariskiOpens_structureSheafMap (N : SmallEtaleNeighborhood xbar) :
    N.scheme.toRingedSpace.ringCatSheaf ⟶
      ((zariskiOpenToEtale N).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology N.scheme)
        (smallEtaleTopology X)).obj (structureSheaf X) where
  hom :=
    { app := fun V ↦
        (forget₂ CommRingCat RingCat).map
          ((Scheme.restrictFunctorΓ (X := N.scheme)).inv.app V ≫
            (zariskiOpen_schemeHom N V.unop).appTop)
      naturality := fun _ _ _ ↦ sorry }

/-- The component of `toZariskiOpens_structureSheafMap` is restriction along
`zariskiOpen_schemeHom`. -/
theorem toZariskiOpens_structureSheafMap_app (N : SmallEtaleNeighborhood xbar)
    (V : (N.scheme.Opens)ᵒᵖ) :
    (toZariskiOpens_structureSheafMap N).hom.app V =
      (forget₂ CommRingCat RingCat).map
        ((Scheme.restrictFunctorΓ (X := N.scheme)).inv.app V ≫
          (zariskiOpen_schemeHom N V.unop).appTop) :=
  sorry

/-- The Zariski `𝒪_U`-module obtained by restricting `F` along the scheme étale neighbourhood
`φ : U ⟶ X`. On a Zariski open `V ⊆ U` its sections are the sections of `F` on the corresponding
object `ofSchemeEtale N V` of `X_étale`, which is the identification `(φ* F)(V) ≅ F(ofSchemeEtale V)`. -/
def pullbackSchemeModule (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    RingedSpace.Modules N.scheme.toRingedSpace :=
  (SheafOfModules.pushforward (toZariskiOpens_structureSheafMap N)).obj F

/-- `pullbackSchemeModule` is module pushforward of `F` along the neighbourhood Zariski
restriction. -/
theorem pullbackSchemeModule_obj (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    pullbackSchemeModule F N = (SheafOfModules.pushforward (toZariskiOpens_structureSheafMap N)).obj F :=
  sorry

/-- Section identification `(φ* F)(V) ⟶ F(ofSchemeEtale V)` induced by module pushforward along
`zariskiOpenToEtale`. -/
def pullbackSchemeModule_sectionHom (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    (U : N.scheme.Opens) :
    (pullbackSchemeModule F N).val.presheaf.obj (op U) ⟶
      F.val.presheaf.obj (op ((zariskiOpenToEtale N).obj U)) :=
  (forget₂ (ModuleCat _) AddCommGrpCat).map
    ((pullbackSchemeModule F N).val.map (𝟙 (op U)))

/-- The Zariski stalk `(φ* F)_u` of the neighbourhood pullback at the image `u` of `ubar`. -/
def pullbackZariskiStalk (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    ModuleCat (N.scheme.presheaf.stalk N.center) :=
  RingedSpace.stalkModuleCat (pullbackSchemeModule F N) N.center

/-- `pullbackZariskiStalk` is the ringed-space module stalk of `pullbackSchemeModule` at the
neighbourhood center. -/
theorem pullbackZariskiStalk_def (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    pullbackZariskiStalk F N =
      RingedSpace.stalkModuleCat (pullbackSchemeModule F N) N.center :=
  sorry

/-- The underlying scheme open of an open neighbourhood of the étale-neighbourhood center. -/
def openNhds_schemeOpens (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) : N.scheme.Opens :=
  ⟨(U.1 : Set N.scheme), U.1.is_open'⟩

/-- `openNhds_schemeOpens` is the scheme open underlying the topological neighbourhood. -/
theorem openNhds_schemeOpens_eq (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) :
    openNhds_schemeOpens N U = ⟨(U.1 : Set N.scheme), U.1.is_open'⟩ :=
  sorry

/-- The image of the neighbourhood geometric point lies in every open neighbourhood of its
center. -/
theorem zariskiOpenFiber_range_subset (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) :
    Set.range (schemeGeometricPoint N).hom ⊆
      Set.range
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).hom :=
  sorry

/-- Canonical lift of `schemeGeometricPoint N` through a Zariski open neighbourhood of the
center, obtained by the open-immersion lifting property of the corresponding site object. -/
def zariskiOpenFiber (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) :
    (Scheme.GeometricPoint.toSmallEtalePoint (schemeGeometricPoint N)).fiber.obj
      ((smallZariskiToSmallEtale N.scheme).obj
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U))) :=
  Over.homMk
    (IsOpenImmersion.lift
      (H :=
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).prop)
      ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).hom
      (schemeGeometricPoint N).hom (zariskiOpenFiber_range_subset N U) :
      Spec (.of (schemeGeometricPoint N).K) ⟶
        ((smallZariskiToSmallEtale N.scheme).obj
          ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U))).left)
    (IsOpenImmersion.lift_fac
      (H :=
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).prop)
      ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).hom
      (schemeGeometricPoint N).hom (zariskiOpenFiber_range_subset N U))

/-- The underlying scheme morphism of `zariskiOpenFiber` is the open-immersion lift of the
neighbourhood geometric point. -/
theorem zariskiOpenFiber_left (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) :
    (zariskiOpenFiber N U).left =
      IsOpenImmersion.lift
        (H :=
          ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).prop)
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).hom
        (schemeGeometricPoint N).hom (zariskiOpenFiber_range_subset N U) :=
  sorry

end GeometricPoint.SmallEtaleNeighborhood

namespace Modules

open GeometricPoint.SmallEtaleNeighborhood
open etaleLocalRing_etaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}

/-- Open-neighbourhood diagram of the Zariski module `pullbackSchemeModule F N` at the
neighbourhood center. -/
def pullbackZariskiStalkDiagram (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    (OpenNhds (X := (N.scheme : TopCat)) N.center)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (OpenNhds.inclusion (X := (N.scheme : TopCat)) N.center).op ⋙
    (pullbackSchemeModule F N).val.presheaf

/-- Germ of a Zariski section of `pullbackSchemeModule F N` into the étale stalk `F_{xbar}`,
using the section identification with `F` and the canonical fiber lift of
`schemeGeometricPoint N`. -/
def pullbackSectionToEtaleStalk (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) :
    (pullbackSchemeModule F N).val.presheaf.obj (op U.1) ⟶
      AddCommGrpCat.of (stalkModuleCat xbar F) :=
  pullbackSchemeModule_sectionHom F N (openNhds_schemeOpens N U) ≫
    (toSmallEtalePoint xbar).toPresheafFiber
      ((zariskiOpenToEtale N).obj (openNhds_schemeOpens N U))
      (SmallEtaleNeighborhood.ofSchemeFiber N (zariskiOpenFiber N U))
      F.val.presheaf

/-- The additive comparison from the Zariski stalk of `φ* F` to the étale stalk `F_{xbar}`. -/
def pullbackStalkAddHom (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (pullbackSchemeModule F N).val.presheaf N.center ⟶
      AddCommGrpCat.of (stalkModuleCat xbar F) :=
  colimit.desc (pullbackZariskiStalkDiagram F N)
    { pt := AddCommGrpCat.of (stalkModuleCat xbar F)
      ι :=
        { app := fun U ↦ pullbackSectionToEtaleStalk F N U.unop
          naturality := fun _ _ _ ↦ sorry } }

/-- The `𝒪_{U,u}`-linear comparison from the Zariski stalk of `φ* F` to the étale stalk
`F_{xbar}`, after restricting scalars along `fromZariskiStalk`. -/
def pullbackStalkUnitHom (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    pullbackZariskiStalk F N ⟶
      (restrictScalars (fromZariskiStalk N)).obj (stalkModuleCat xbar F) :=
  (semilinearMapAddEquiv (fromZariskiStalk N)
      (pullbackZariskiStalk F N) (stalkModuleCat xbar F))
    { toFun := (pullbackStalkAddHom F N).hom
      map_add' := (pullbackStalkAddHom F N).hom.map_add
      map_smul' := sorry }

/-- `pullbackStalkUnitHom` is `𝒪_{U,u}`-linear. -/
theorem pullbackStalkUnitHom_smul (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    (r : N.scheme.presheaf.stalk N.center) (m : pullbackZariskiStalk F N) :
    pullbackStalkUnitHom F N (r • m) =
      fromZariskiStalk N r • pullbackStalkUnitHom F N m :=
  sorry

/-- Canonical comparison
`(φ* F)_u ⊗_{𝒪_{U,u}} 𝒪_{X, xbar} ⟶ F_{xbar}`
obtained by extending scalars along `fromZariskiStalk`. -/
def pullbackStalkTensorHom (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    (extendScalars (fromZariskiStalk N)).obj (pullbackZariskiStalk F N) ⟶
      stalkModuleCat xbar F :=
  ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (fromZariskiStalk N)
    (pullbackStalkUnitHom F N)

/-- For a quasi-coherent module sheaf, extending the Zariski stalk on a scheme étale
neighbourhood to the geometric étale local ring gives the geometric module stalk via the
canonical section-to-germ comparison. -/
instance pullbackStalkTensorHom_isIso (F : X.Modules) [F.IsQuasicoherent]
    (xbar : GeometricPoint X) (N : SmallEtaleNeighborhood xbar) :
    IsIso (pullbackStalkTensorHom F N) := sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
