module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap92.«92_28_0_1_Transitivity»

/-!
# Stalks of lifted étale modules at geometric points

Universe-lifted `𝒪_X`-modules (`CommModules`) take values in `RingCat.{u + 1}`.  Their
module stalks at a geometric point are obtained from the site-point stalk functor on
the `ULift` of the small étale fiber, then restricted back to the étale local ring
`𝒪_{X, x̄}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Cotangent

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-- The small étale site-point of a geometric point, with fiber values lifted to
`Type (u + 1)` so that `sheafModuleStalkFunctor` applies to `CommModules`. -/
def toSmallEtalePointSucc {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    (smallEtaleTopology X).Point.{u + 1} where
  fiber := (toSmallEtalePoint xbar).fiber ⋙ uliftFunctor.{u + 1, u}
  isCofiltered := sorry
  initiallySmall := sorry
  jointly_surjective := sorry

/-- The fiber of `toSmallEtalePointSucc` is the `ULift` of the ordinary small étale fiber. -/
theorem toSmallEtalePointSucc_fiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    (toSmallEtalePointSucc xbar).fiber =
      (toSmallEtalePoint xbar).fiber ⋙ uliftFunctor.{u + 1, u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebra structure on `𝒪_{X, x̄}` over `𝒪_{Y, ȳ}` induced by a morphism `X ⟶ Y`. -/
instance algebraEtaleLocalRingMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    Algebra (etaleLocalRing Y (xbar.map f)) (etaleLocalRing X xbar) :=
  (etaleLocalRingMap f xbar).toAlgebra

/-- `algebraEtaleLocalRingMap` is the algebra of `etaleLocalRingMap`. -/
theorem algebraEtaleLocalRingMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    algebraEtaleLocalRingMap f xbar = (etaleLocalRingMap f xbar).toAlgebra :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

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
  sorry

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
  sorry

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
  sorry

/-- The morphism of `CommModules` stalks induced by a morphism of lifted `𝒪_X`-modules. -/
def commModulesStalkMap {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F G : CommModules X} (φ : F ⟶ G) :
    commModulesStalk xbar F ⟶ commModulesStalk xbar G :=
  (commModulesStalkFunctor xbar).map φ

/-- `commModulesStalkMap` is the stalk functor applied to a morphism of modules. -/
theorem commModulesStalkMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    {F G : CommModules X} (φ : F ⟶ G) :
    commModulesStalkMap xbar φ = (commModulesStalkFunctor xbar).map φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
