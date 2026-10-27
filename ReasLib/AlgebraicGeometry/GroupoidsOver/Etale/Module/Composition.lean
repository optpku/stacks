/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Composition

/-!
# Composition and 2-isomorphism transport of étale module inverse image

The total-functor composition and 2-isomorphisms identify the corresponding
inverse-image functors, compatibly with their structure-sheaf maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- A composite of total functors is continuous for associated étale topologies. -/
instance toFunctor_comp_isContinuous_etale {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    (toFunctor h ⋙ toFunctor k).IsContinuous X.etaleTopology Z.etaleTopology :=
  Functor.isContinuous_comp (toFunctor h) (toFunctor k)
    X.etaleTopology Y.etaleTopology Z.etaleTopology

/-- The composite structure-sheaf map along `toFunctor h ⋙ toFunctor k`. -/
def etaleSiteHom_structureSheafMap_compData {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    (etaleRingedSite X).structureSheaf ⟶
      ((toFunctor h ⋙ toFunctor k).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Z.etaleTopology).obj (etaleRingedSite Z).structureSheaf :=
  (etaleSiteHom h).structureSheafMap ≫
    ((toFunctor h).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).map (etaleSiteHom k).structureSheafMap

/-- Module inverse image along a composite, before transporting the total functor. -/
def etaleModuleInverseImage_comp₀ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleModuleInverseImage k ⋙ etaleModuleInverseImage h ≅
      SheafOfModules.pushforward (etaleSiteHom_structureSheafMap_compData h k) :=
  SheafOfModules.pushforwardComp (F := toFunctor h) (G := toFunctor k)
    (J := X.etaleTopology) (K := Y.etaleTopology) (K' := Z.etaleTopology)
    (etaleSiteHom h).structureSheafMap
    (etaleSiteHom k).structureSheafMap

/-- Transport of composite inverse image along the real total-functor composition
isomorphism. -/
def etaleModuleInverseImage_comp₁ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    SheafOfModules.pushforward (etaleSiteHom_structureSheafMap_compData h k) ≅
      SheafOfModules.pushforward
        (etaleSiteHom_structureSheafMap_compData h k ≫
          (sheafPushforwardContinuousNatTrans
              (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
              RingCat.{u} X.etaleTopology Z.etaleTopology).app
            (etaleRingedSite Z).structureSheaf) :=
  SheafOfModules.pushforwardNatIso (etaleSiteHom_structureSheafMap_compData h k)
    (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)

/-- The transported composite structure-sheaf map agrees with the structure-sheaf
map of the composite 1-morphism. -/
theorem etaleSiteHom_structureSheafMap_comp {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleSiteHom_structureSheafMap_compData h k ≫
        (sheafPushforwardContinuousNatTrans
            (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
            RingCat.{u} X.etaleTopology Z.etaleTopology).app
          (etaleRingedSite Z).structureSheaf =
      (etaleSiteHom (h ≫ k)).structureSheafMap :=
  sorry

/-- Align the transported composite inverse image with inverse image along the
composite 1-morphism. -/
def etaleModuleInverseImage_comp₂ {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    SheafOfModules.pushforward
        (etaleSiteHom_structureSheafMap_compData h k ≫
          (sheafPushforwardContinuousNatTrans
              (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).hom
              RingCat.{u} X.etaleTopology Z.etaleTopology).app
            (etaleRingedSite Z).structureSheaf) ≅
      etaleModuleInverseImage (h ≫ k) :=
  SheafOfModules.pushforwardCongr (etaleSiteHom_structureSheafMap_comp h k)

/-- Inverse image of étale modules along a composite 1-morphism is the composite
of the inverse images, via `pushforwardComp` and the real total-functor
composition isomorphism. -/
def etaleModuleInverseImage_comp {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleModuleInverseImage k ⋙ etaleModuleInverseImage h ≅
      etaleModuleInverseImage (h ≫ k) :=
  etaleModuleInverseImage_comp₀ h k ≪≫
    etaleModuleInverseImage_comp₁ h k ≪≫ etaleModuleInverseImage_comp₂ h k

/-- The structure-sheaf map of `h₂` transported along `toFunctorIso e` agrees with
the structure-sheaf map of `h₁`. -/
theorem etaleSiteHom_structureSheafMap_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y}
    (e : h₁ ≅ h₂) :
    (etaleSiteHom h₂).structureSheafMap ≫
        (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
            X.etaleTopology Y.etaleTopology).app
          (etaleRingedSite Y).structureSheaf =
      (etaleSiteHom h₁).structureSheafMap :=
  sorry

/-- Transport of inverse image along the real total-functor isomorphism. -/
def etaleModuleInverseImage_iso₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    etaleModuleInverseImage h₂ ≅
      SheafOfModules.pushforward
        ((etaleSiteHom h₂).structureSheafMap ≫
          (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
              X.etaleTopology Y.etaleTopology).app
            (etaleRingedSite Y).structureSheaf) :=
  SheafOfModules.pushforwardNatIso (G := toFunctor h₂)
    (J := X.etaleTopology) (K := Y.etaleTopology)
    (etaleSiteHom h₂).structureSheafMap (toFunctorIso e)

/-- Align the transported inverse image with inverse image along `h₁`. -/
def etaleModuleInverseImage_iso₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    SheafOfModules.pushforward
        ((etaleSiteHom h₂).structureSheafMap ≫
          (sheafPushforwardContinuousNatTrans (toFunctorIso e).hom RingCat.{u}
              X.etaleTopology Y.etaleTopology).app
            (etaleRingedSite Y).structureSheaf) ≅
      etaleModuleInverseImage h₁ :=
  SheafOfModules.pushforwardCongr (etaleSiteHom_structureSheafMap_iso e)

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of étale module
inverse images, via the underlying total-functor isomorphism `toFunctorIso`. -/
def etaleModuleInverseImage_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    etaleModuleInverseImage h₁ ≅ etaleModuleInverseImage h₂ :=
  (etaleModuleInverseImage_iso₀ e ≪≫ etaleModuleInverseImage_iso₁ e).symm

/-- 2-cell transport `a^* g^* ≅ f^*` on étale modules. -/
def etaleModuleInverseImage_twoCell {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f) :
    etaleModuleInverseImage g ⋙ etaleModuleInverseImage a ≅
      etaleModuleInverseImage f :=
  etaleModuleInverseImage_comp a g ≪≫ etaleModuleInverseImage_iso φ

end AlgebraicGeometry.GroupoidsOver
