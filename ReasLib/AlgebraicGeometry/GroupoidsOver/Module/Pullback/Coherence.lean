/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage

/-! # Composition and two-cell coherence for module pullback -/

@[expose] public section
set_option backward.privateInPublic true
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- The cartesian total functors of `f` and `g` compose to the cartesian total functor
of the composite, after identifying each with `toFunctor`. -/
def cartesianToFunctor_compIso {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (toCartesianBasedFunctor f).toFunctor ⋙ (toCartesianBasedFunctor g).toFunctor ≅
      (toCartesianBasedFunctor (f ≫ g)).toFunctor :=
  eqToIso
      (congrArg₂ (fun F G => F ⋙ G) (cartesian_toFunctor_eq f)
        (cartesian_toFunctor_eq g)) ≪≫
    FullSubbicategory.toFunctor.compIso f g ≪≫
      eqToIso (cartesian_toFunctor_eq (f ≫ g)).symm

/-- Composite of cartesian total functors is continuous for inherited fppf topologies. -/
instance cartesianToFunctor_comp_isContinuous {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((toCartesianBasedFunctor f).toFunctor ⋙
        (toCartesianBasedFunctor g).toFunctor).IsContinuous
      (inheritedFppfTopology X) (inheritedFppfTopology Z) :=
  Functor.isContinuous_comp (toCartesianBasedFunctor f).toFunctor
    (toCartesianBasedFunctor g).toFunctor (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (inheritedFppfTopology Z)

/-- The composite structure-sheaf map along cartesian total functors of `f` and `g`. -/
private def structureSheafMap_compData {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheaf X ⟶
      (((toCartesianBasedFunctor f).toFunctor ⋙
          (toCartesianBasedFunctor g).toFunctor).sheafPushforwardContinuous RingCat.{u}
        (inheritedFppfTopology X) (inheritedFppfTopology Z)).obj (structureSheaf Z) :=
  structureSheafMap f ≫
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous RingCat.{u}
        (inheritedFppfTopology X) (inheritedFppfTopology Y)).map (structureSheafMap g)

/-- Module inverse image along a composite, before transporting the total functor. -/
private def modulePullback_comp₀ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g ⋙ modulePullback f ≅
      SheafOfModules.pushforward (structureSheafMap_compData f g) :=
  SheafOfModules.pushforwardComp (structureSheafMap f) (structureSheafMap g)

/-- Transport of composite inverse image along the cartesian total-functor composition
isomorphism. -/
private def modulePullback_comp₁ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pushforward (structureSheafMap_compData f g) ≅
      SheafOfModules.pushforward
        (structureSheafMap_compData f g ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_compIso f g).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
            (structureSheaf Z)) :=
  SheafOfModules.pushforwardNatIso (structureSheafMap_compData f g)
    (cartesianToFunctor_compIso f g)

/-- The transported composite structure-sheaf map agrees with the structure-sheaf map
of the composite 1-morphism. -/
private theorem structureSheafMap_comp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSheafMap_compData f g ≫
        (Functor.sheafPushforwardContinuousNatTrans
            (cartesianToFunctor_compIso f g).hom RingCat.{u}
            (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
          (structureSheaf Z) =
      structureSheafMap (f ≫ g) :=
  sorry

/-- Align the transported composite inverse image with inverse image along the composite. -/
private def modulePullback_comp₂ {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.pushforward
        (structureSheafMap_compData f g ≫
          (Functor.sheafPushforwardContinuousNatTrans
              (cartesianToFunctor_compIso f g).hom RingCat.{u}
              (inheritedFppfTopology X) (inheritedFppfTopology Z)).app
            (structureSheaf Z)) ≅
      modulePullback (f ≫ g) :=
  SheafOfModules.pushforwardCongr (structureSheafMap_comp f g)

/-- Inverse image of modules along a composite 1-morphism is the composite of the
inverse images. -/
def modulePullback_comp {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g ⋙ modulePullback f ≅ modulePullback (f ≫ g) :=
  modulePullback_comp₀ f g ≪≫ modulePullback_comp₁ f g ≪≫ modulePullback_comp₂ f g

/-- The cartesian total functor of `h₂` transported along `toFunctorIso e` agrees with
the cartesian total functor of `h₁`. -/
private def cartesianToFunctorIso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    (toCartesianBasedFunctor h₁).toFunctor ≅ (toCartesianBasedFunctor h₂).toFunctor :=
  eqToIso (cartesian_toFunctor_eq h₁) ≪≫ toFunctorIso e ≪≫
    (eqToIso (cartesian_toFunctor_eq h₂)).symm

/-- Transport of inverse image along the real total-functor isomorphism. -/
private def modulePullback_iso₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    modulePullback h₂ ≅
      SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorIso e).hom
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) :=
  SheafOfModules.pushforwardNatIso (structureSheafMap h₂) (cartesianToFunctorIso e)

/-- The structure-sheaf map of `h₂` transported along `cartesianToFunctorIso e` agrees
with the structure-sheaf map of `h₁`. -/
private theorem structureSheafMap_iso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    structureSheafMap h₂ ≫
        (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorIso e).hom
            RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
          (structureSheaf Y) =
      structureSheafMap h₁ :=
  sorry

/-- Align the transported inverse image with inverse image along `h₁`. -/
private def modulePullback_iso₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorIso e).hom
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) ≅
      modulePullback h₁ :=
  SheafOfModules.pushforwardCongr (structureSheafMap_iso e)

/-- A 2-isomorphism of 1-morphisms induces an isomorphism of module inverse images. -/
def modulePullbackIso {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂) :
    modulePullback h₁ ≅ modulePullback h₂ :=
  (modulePullback_iso₀ e ≪≫ modulePullback_iso₁ e).symm

/-- The total-functor transformation of a `2`-cell, after identifying cartesian
total functors with `toFunctor`. -/
private def cartesianToFunctorHom {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    (toCartesianBasedFunctor h₁).toFunctor ⟶ (toCartesianBasedFunctor h₂).toFunctor :=
  eqToHom (cartesian_toFunctor_eq h₁) ≫ toNatTrans α ≫
    eqToHom (cartesian_toFunctor_eq h₂).symm

/-- Contravariant transport of inverse image along the total-functor map of a
`2`-cell. -/
private def modulePullback_hom₀ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    modulePullback h₂ ⟶
      SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorHom α)
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) :=
  SheafOfModules.pushforwardNatTrans (structureSheafMap h₂) (cartesianToFunctorHom α)

/-- The structure-sheaf map of `h₂` transported along `cartesianToFunctorHom α`
agrees with the structure-sheaf map of `h₁`. -/
private theorem structureSheafMap_hom {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    structureSheafMap h₂ ≫
        (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorHom α)
            RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
          (structureSheaf Y) =
      structureSheafMap h₁ :=
  sorry

/-- Align the transported inverse image with inverse image along `h₁`. -/
private def modulePullback_hom₁ {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    SheafOfModules.pushforward
        (structureSheafMap h₂ ≫
          (Functor.sheafPushforwardContinuousNatTrans (cartesianToFunctorHom α)
              RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)).app
            (structureSheaf Y)) ⟶
      modulePullback h₁ :=
  (SheafOfModules.pushforwardCongr (structureSheafMap_hom α)).hom

/-- A `2`-cell of 1-morphisms induces a morphism of module inverse images, without
inverting the cell. -/
def modulePullbackHom {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    modulePullback h₂ ⟶ modulePullback h₁ :=
  modulePullback_hom₀ α ≫ modulePullback_hom₁ α

/-- `modulePullbackHom` is the contravariant pushforward map of the `2`-cell. -/
theorem modulePullbackHom_eq {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (α : h₁ ⟶ h₂) :
    modulePullbackHom α = modulePullback_hom₀ α ≫ modulePullback_hom₁ α :=
  rfl

/-- The coefficient isomorphism of `structureSheafMap f` at an object of `X`. -/
def structureSheafMap_appIso {X Y : GroupoidsOver S} (f : X ⟶ Y) (x : X.totalᵒᵖ) :
    (structureSheaf X).obj.obj x ≅ (inverseImageStructureSheaf f).obj.obj x :=
  ((sheafToPresheaf (inheritedFppfTopology X) RingCat.{u}).mapIso
      (structureSheafIso f).symm).app x

/-- The ring equivalence underlying `structureSheafMap_appIso`. -/
def structureSheafMap_appRingEquiv {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (x : X.totalᵒᵖ) :
    (structureSheaf X).obj.obj x ≃+* (inverseImageStructureSheaf f).obj.obj x :=
  CategoryTheory.Iso.ringCatIsoToRingEquiv (structureSheafMap_appIso f x)

/-- Evaluation of module inverse image along `f` is restriction of scalars of
evaluation at the cartesian image object. -/
theorem modulePullback_eval_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheaf Y)) (x : X.total) :
    ((modulePullback f).obj F).val.obj (op x) =
      (ModuleCat.restrictScalars
          ((structureSheafMap f).hom.app (op x)).hom).obj
        (F.val.obj (op ((toCartesianBasedFunctor f).toFunctor.obj x))) :=
  rfl

/-- Evaluation of module inverse image along `f` is restriction of scalars of
evaluation at the cartesian image object. -/
def modulePullback_evalIso {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheaf Y)) (x : X.total) :
    ((modulePullback f).obj F).val.obj (op x) ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap f).hom.app (op x)).hom).obj
        (F.val.obj (op ((toCartesianBasedFunctor f).toFunctor.obj x))) :=
  eqToIso (modulePullback_eval_eq f F x)

end AlgebraicGeometry.GroupoidsOver
