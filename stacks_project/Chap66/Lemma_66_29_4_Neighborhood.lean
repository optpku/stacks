/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Category.TopCat.OpenNhds
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap66.Lemma_66_22_1_Comparison
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_4_Stalk

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

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}

/-- The reconstructed scheme point retains its original algebraically closed field. -/
instance schemeGeometricPoint_isAlgClosed (N : SmallEtaleNeighborhood xbar) :
    IsAlgClosed N.schemeGeometricPoint.K := N.schemeGeometricPoint.isAlgClosed

/-- The functor sending a scheme étale over the neighbourhood scheme to the corresponding object
of the small étale site of `X`. -/
def ofSchemeEtaleFunctor (N : SmallEtaleNeighborhood xbar) :
    N.scheme.Etale ⥤ smallEtaleSite X where
  obj W := ofSchemeEtale N W
  map {W W'} f :=
    (etaleRestriction N.toSite.hom).map
      (MorphismProperty.CostructuredArrow.homMk
        (Over.homMk f.left sorry : (AlgebraicSpace.ofSchemeEtale W).left ⟶
          (AlgebraicSpace.ofSchemeEtale W').left)
        trivial sorry)
  map_id := sorry
  map_comp := sorry

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

/-- The Zariski-to-étale comparison of the neighbourhood scheme is a morphism of sites into the
small étale site of `X`. -/
instance zariskiOpenToEtale_isMorphismOfSites (N : SmallEtaleNeighborhood xbar) :
    IsMorphismOfSites (Opens.grothendieckTopology N.scheme)
      (smallEtaleTopology X) (zariskiOpenToEtale N) :=
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
    (RingedSpace.opensRingedSite N.scheme.toRingedSpace).structureSheaf ⟶
      ((zariskiOpenToEtale N).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology N.scheme)
        (smallEtaleTopology X)).obj (structureSheaf X) where
  hom :=
    { app := fun V ↦
        (forget₂ CommRingCat RingCat).map
          ((Scheme.restrictFunctorΓ (X := N.scheme)).inv.app V ≫
            (zariskiOpen_schemeHom N V.unop).appTop)
      naturality := fun _ _ _ ↦ sorry }

/-- The ringed-site morphism from the small étale site of `X` to the Zariski opens of the
neighbourhood scheme. -/
def toZariskiOpens (N : SmallEtaleNeighborhood xbar) :
    RingedSite.Hom (ringedSite X)
      (RingedSpace.opensRingedSite N.scheme.toRingedSpace) where
  base := zariskiOpenToEtale N
  structureSheafMap := toZariskiOpens_structureSheafMap N

/-- The base functor of `toZariskiOpens` is `zariskiOpenToEtale`. -/
theorem toZariskiOpens_base (N : SmallEtaleNeighborhood xbar) :
    (toZariskiOpens N).base = zariskiOpenToEtale N :=
  sorry

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
  (toZariskiOpens N).modulePushforward.obj F

/-- `pullbackSchemeModule` is module pushforward of `F` along the neighbourhood Zariski
restriction. -/
theorem pullbackSchemeModule_obj (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    pullbackSchemeModule F N = (toZariskiOpens N).modulePushforward.obj F :=
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

/-- Canonical lift of `schemeGeometricPoint N` through a Zariski open neighbourhood of the
center, obtained by the open-immersion lifting property of the corresponding site object. -/
def zariskiOpenFiber (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) :
    (Scheme.pointSmallEtale (schemeGeometricPoint N).hom).fiber.obj
      ((smallZariskiToSmallEtale N.scheme).obj
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U))) :=
  Over.homMk
    (IsOpenImmersion.lift
      (H :=
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).prop)
      ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).hom
      (schemeGeometricPoint N).hom sorry :
      Spec (.of (schemeGeometricPoint N).K) ⟶
        ((smallZariskiToSmallEtale N.scheme).obj
          ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U))).left)
    sorry

/-- The underlying scheme morphism of `zariskiOpenFiber` is the open-immersion lift of the
neighbourhood geometric point. -/
theorem zariskiOpenFiber_left (N : SmallEtaleNeighborhood xbar)
    (U : OpenNhds (X := (N.scheme : TopCat)) N.center) :
    (zariskiOpenFiber N U).left =
      IsOpenImmersion.lift
        (H :=
          ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).prop)
        ((Scheme.smallZariskiOpenFunctor N.scheme).obj (openNhds_schemeOpens N U)).hom
        (schemeGeometricPoint N).hom sorry :=
  sorry

/-- The étale neighbourhood obtained by base-changing `V` along the structure morphism of `N`. -/
def pullbackNeighborhood (N : SmallEtaleNeighborhood xbar) {V : smallEtaleSite X}
    (l : OverLift xbar V) : SmallEtaleNeighborhood xbar :=
  SmallEtaleNeighborhood.of (ofSchemeEtale N (toSchemeEtale N V))
    (ofSchemeFiber N (toSchemeFiber N l)).hom
    (ofSchemeFiber N (toSchemeFiber N l)).fac

/-- The scheme morphism from the base-changed neighbourhood to the original neighbourhood
scheme. -/
def pullbackNeighborhood_schemeHom (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X) :
    (toSchemeEtale N V).left ⟶ N.scheme :=
  (toSchemeEtale N V).hom

/-- The ringed-space morphism underlying `pullbackNeighborhood_schemeHom`. -/
def pullbackNeighborhood_ringedHom (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X) :
    (toSchemeEtale N V).left.toRingedSpace ⟶ N.scheme.toRingedSpace :=
  (pullbackNeighborhood_schemeHom N V).toLRSHom.toShHom

/-- The morphism in the small étale site of `X` from the base-changed neighbourhood to `V`. -/
def pullbackNeighborhood_toSite (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X) :
    ofSchemeEtale N (toSchemeEtale N V) ⟶ V :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (toSchemeEtale_schemeHom N V) sorry) trivial sorry

end GeometricPoint.SmallEtaleNeighborhood

namespace Modules

open GeometricPoint.SmallEtaleNeighborhood
open etaleLocalRing_etaleNeighborhood
open AlgebraicGeometry.RingedSpace.Hom

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

/-- The étale neighbourhood associated to a site-point lift of `xbar`. -/
def neighborhoodOfLift {V : smallEtaleSite X}
    (l : (toSmallEtalePoint xbar).fiber.obj V) :
    SmallEtaleNeighborhood xbar :=
  SmallEtaleNeighborhood.of V l.hom l.fac

/-- The adjunction unit `M ⟶ Restrict(M ⊗ S)` associated to `fromZariskiStalk`. -/
def pullbackStalkTensorUnit (F : X.Modules) (N : SmallEtaleNeighborhood xbar) :
    pullbackZariskiStalk F N ⟶
      (restrictScalars (fromZariskiStalk N)).obj
        ((extendScalars (fromZariskiStalk N)).obj (pullbackZariskiStalk F N)) :=
  (extendRestrictScalarsAdj (fromZariskiStalk N)).unit.app (pullbackZariskiStalk F N)

/-- Restriction of a section of `F` along the projection from the base change of `V` to `N`. -/
def sectionRestrictToPullback (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    (V : smallEtaleSite X) :
    F.val.presheaf.obj (op V) ⟶
      F.val.presheaf.obj
        (op (SmallEtaleNeighborhood.ofSchemeEtale N
          (SmallEtaleNeighborhood.toSchemeEtale N V))) :=
  F.val.presheaf.map (pullbackNeighborhood_toSite N V).op

/-- Local ring map of the neighbourhood scheme morphism, from `𝒪_{U,u}` to the Zariski local
ring of the base-changed neighbourhood. -/
def pullbackNeighborhood_stalkMap (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X)
    (l : OverLift xbar V) :
    N.scheme.presheaf.stalk
        ((pullbackNeighborhood_ringedHom N V).hom.base
          (pullbackNeighborhood N l).center) →+*
      (SmallEtaleNeighborhood.toSchemeEtale N V).left.presheaf.stalk
        (pullbackNeighborhood N l).center :=
  ((pullbackNeighborhood_ringedHom N V).hom.stalkMap
    (pullbackNeighborhood N l).center).hom

/-- Inverse image of `pullbackSchemeModule F N` along the neighbourhood scheme morphism. -/
def pullbackSchemeModuleInverseImage (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    (V : smallEtaleSite X) :
    RingedSpace.Modules
      (SmallEtaleNeighborhood.toSchemeEtale N V).left.toRingedSpace :=
  (RingedSpace.Hom.pullback (pullbackNeighborhood_ringedHom N V)).obj
    (pullbackSchemeModule F N)

/-- The Zariski stalk of the inverse image of `φ* F` at the center of a base-changed
neighbourhood. -/
def pullbackInverseImageStalk (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    {V : smallEtaleSite X} (l : OverLift xbar V) :
    ModuleCat
      ((SmallEtaleNeighborhood.toSchemeEtale N V).left.presheaf.stalk
        (pullbackNeighborhood N l).center) :=
  RingedSpace.stalkModuleCat
    (pullbackSchemeModuleInverseImage F N V)
    (pullbackNeighborhood N l).center

/-- The Zariski stalk of `φ* F` at the image of the base-changed center. -/
def pullbackZariskiStalkAtImage (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    {V : smallEtaleSite X} (l : OverLift xbar V) :
    ModuleCat
      (N.scheme.presheaf.stalk
        ((pullbackNeighborhood_ringedHom N V).hom.base
          (pullbackNeighborhood N l).center)) :=
  RingedSpace.stalkModuleCat (pullbackSchemeModule F N)
    ((pullbackNeighborhood_ringedHom N V).hom.base
      (pullbackNeighborhood N l).center)

/-- Scalar-extension associator along `pullbackNeighborhood_stalkMap` followed by
`fromZariskiStalk` of the base-changed neighbourhood. -/
def pullbackStalkTensorAssociator (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    {V : smallEtaleSite X} (l : OverLift xbar V) :
    (extendScalars (fromZariskiStalk (pullbackNeighborhood N l))).obj
        ((extendScalars (pullbackNeighborhood_stalkMap N V l)).obj
          (pullbackZariskiStalkAtImage F N l)) ⟶
      (extendScalars
        ((fromZariskiStalk (pullbackNeighborhood N l)).comp
          (pullbackNeighborhood_stalkMap N V l))).obj
        (pullbackZariskiStalkAtImage F N l) :=
  (extendScalarsComp (pullbackNeighborhood_stalkMap N V l)
      (fromZariskiStalk (pullbackNeighborhood N l))).inv.app
    (pullbackZariskiStalkAtImage F N l)

/-- Canonical comparison of neighbourhood tensors along the scheme morphism of a base change
of `V` to `N`, obtained from the ringed-space pullback-stalk inverse and the scalar-extension
associator. -/
def pullbackStalkTensorComparisonInv (F : X.Modules) (N : SmallEtaleNeighborhood xbar)
    {V : smallEtaleSite X} (l : OverLift xbar V) :
    (extendScalars (fromZariskiStalk (pullbackNeighborhood N l))).obj
        (pullbackInverseImageStalk F N l) ⟶
      (extendScalars
        ((fromZariskiStalk (pullbackNeighborhood N l)).comp
          (pullbackNeighborhood_stalkMap N V l))).obj
        (pullbackZariskiStalkAtImage F N l) :=
  (extendScalars (fromZariskiStalk (pullbackNeighborhood N l))).map
      (pullbackStalkComparisonInv
        (pullbackNeighborhood_ringedHom N V)
        (pullbackSchemeModule F N)
        (pullbackNeighborhood N l).center) ≫
    pullbackStalkTensorAssociator F N l

end Modules

end AlgebraicGeometry.AlgebraicSpace
