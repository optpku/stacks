/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.Transitivity

/-!
# Stalks of lifted étale modules at geometric points
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry.AlgebraicSpace.Cotangent

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

/-- Type-valued diagram of étale sections along lifts of a geometric point. -/
def etaleSectionDiagram {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    (toSmallEtalePoint xbar).fiber.Elementsᵒᵖ ⥤ Type u :=
  (CategoryOfElements.π (toSmallEtalePoint xbar).fiber).op ⋙
    (structureSheaf X).obj ⋙ forget RingCat.{u}

/-- Identification of the étale local ring with the type-valued colimit of étale sections. -/
def etaleLocalRingForgetColimitIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    (forget RingCat.{u}).obj
        ((toSmallEtalePoint xbar).presheafFiber.obj (structureSheaf X).obj) ≅
      colimit (etaleSectionDiagram xbar) :=
  preservesColimitIso (forget RingCat.{u})
    ((CategoryOfElements.π (toSmallEtalePoint xbar).fiber).op ⋙ (structureSheaf X).obj)

/-- Universe lift of the type-valued colimit of étale sections. -/
def uliftEtaleSectionColimitIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    uliftFunctor.{u + 1, u}.obj (colimit (etaleSectionDiagram xbar)) ≅
      colimit (etaleSectionDiagram xbar ⋙ uliftFunctor.{u + 1, u}) :=
  preservesColimitIso (uliftFunctor.{u + 1, u}) (etaleSectionDiagram xbar)

/-- Cocone of lifted étale sections toward the coefficient stalk of `CommModules`. -/
def liftedStalkCocone {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    Cocone (etaleSectionDiagram xbar ⋙ uliftFunctor.{u + 1, u}) where
  pt := (toSmallEtalePointSucc xbar).stalkRing (ringOf (commStructureSheafLift X))
  ι :=
    { app := fun e ↦
        TypeCat.ofHom fun x ↦
          RingCat.Hom.hom
              ((toSmallEtalePointSucc xbar).toPresheafFiber e.unop.1 (ULift.up e.unop.2)
                (ringOf (commStructureSheafLift X)).obj)
            x
      naturality := fun _ _ _ ↦ sorry }

/-- The colimit of lifted étale sections maps to the `CommModules` coefficient stalk. -/
def uliftSectionColimitToLiftedStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    colimit (etaleSectionDiagram xbar ⋙ uliftFunctor.{u + 1, u}) ⟶
      ((toSmallEtalePointSucc xbar).stalkRing (ringOf (commStructureSheafLift X))) :=
  colimit.desc _ (liftedStalkCocone xbar)

/-- Underlying function of the coefficient-ring map from `𝒪_{X, x̄}` to the lifted stalk. -/
def etaleLocalRingToLiftedStalk_toFun {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) (r : etaleLocalRing X xbar) :
    ((toSmallEtalePointSucc xbar).stalkRing (ringOf (commStructureSheafLift X))) :=
  uliftSectionColimitToLiftedStalk xbar
    ((uliftEtaleSectionColimitIso xbar).hom
      (ULift.up ((etaleLocalRingForgetColimitIso xbar).hom r)))

/-- Canonical ring homomorphism from the étale local ring `𝒪_{X, x̄}` to the coefficient
ring of `CommModules` stalks at `x̄`. -/
def etaleLocalRingToLiftedStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    etaleLocalRing X xbar →+*
      ((toSmallEtalePointSucc xbar).stalkRing (ringOf (commStructureSheafLift X))) where
  toFun := etaleLocalRingToLiftedStalk_toFun xbar
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Unfolding of `etaleLocalRingToLiftedStalk` through `ULift.up` and the section colimit. -/
theorem etaleLocalRingToLiftedStalk_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) (r : etaleLocalRing X xbar) :
    etaleLocalRingToLiftedStalk xbar r =
      etaleLocalRingToLiftedStalk_toFun xbar r :=
  rfl

/-- The stalk functor of `CommModules` at a geometric point, valued in modules over
`𝒪_{X, x̄}`. -/
def commModulesStalkFunctor {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    CommModules X ⥤ ModuleCat.{u + 1} (etaleLocalRing X xbar) :=
  (toSmallEtalePointSucc xbar).sheafModuleStalkFunctor (ringOf (commStructureSheafLift X)) ⋙
    ModuleCat.restrictScalars (etaleLocalRingToLiftedStalk xbar)

/-- Unfolding of `commModulesStalkFunctor` as restriction of the site-point module stalk. -/
theorem commModulesStalkFunctor_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    commModulesStalkFunctor xbar =
      (toSmallEtalePointSucc xbar).sheafModuleStalkFunctor
          (ringOf (commStructureSheafLift X)) ⋙
        ModuleCat.restrictScalars (etaleLocalRingToLiftedStalk xbar) :=
  rfl

/-- The stalk of a lifted `𝒪_X`-module at a geometric point, as a module over `𝒪_{X, x̄}`. -/
def commModulesStalk {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (F : CommModules X) : ModuleCat.{u + 1} (etaleLocalRing X xbar) :=
  (commModulesStalkFunctor xbar).obj F

/-- Unfolding of `commModulesStalk` as `restrictScalars` of the site-point module stalk. -/
theorem commModulesStalk_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (F : CommModules X) :
    commModulesStalk xbar F =
      (ModuleCat.restrictScalars (etaleLocalRingToLiftedStalk xbar)).obj
        (((toSmallEtalePointSucc xbar).sheafModuleStalkFunctor
            (ringOf (commStructureSheafLift X))).obj F) :=
  rfl

/-- The morphism of `CommModules` stalks induced by a morphism of lifted `𝒪_X`-modules. -/
def commModulesStalkMap {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F G : CommModules X} (φ : F ⟶ G) :
    commModulesStalk xbar F ⟶ commModulesStalk xbar G :=
  (commModulesStalkFunctor xbar).map φ

/-- `commModulesStalkMap` is the stalk functor applied to a morphism of modules. -/
theorem commModulesStalkMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F G : CommModules X} (φ : F ⟶ G) :
    commModulesStalkMap xbar φ = (commModulesStalkFunctor xbar).map φ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Cotangent
