/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Skyscraper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Indiscrete

/-!
# Skyscraper module sheaves on ringed spaces

This module specializes the point-space and skyscraper-sheaf constructions to module sheaves over
the structure sheaf of a ringed space.

## API

- The equivalence between modules over a stalk ring and module sheaves on the associated
  one-point ringed space is not rebuilt here: `pointRingedSpace x` is definitionally
  `RingedPoint.of (X.presheaf.stalk x)`, so the canonical owner `RingedPoint.Module.equivalence`
  is used directly.
- `AlgebraicGeometry.RingedSpace.Module.Skyscraper` owns skyscraper module sheaves on the ambient
  ringed space, their specialization maps, and the point-pullback adjunction.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}

open CategoryTheory.Limits

/-- The pullback model of the module-stalk functor at `x`: pull a module sheaf back along
`pointInclusion x`, then identify module sheaves on the resulting one-point ringed space
`pointRingedSpace x = RingedPoint.of (X.presheaf.stalk x)` with modules over `X.presheaf.stalk x`. -/
public noncomputable def RingedSpace.Module.pointPullbackFunctor (x : X) :
    X.Modules ⥤ ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) :=
  RingedSpace.Hom.pullback (pointInclusion x) ⋙
    RingedPoint.Module.topSectionsFunctor (X.presheaf.stalk x)

/-- The pullback model of the module-stalk functor is additive. -/
@[stacks 0FKS "additivity of the point-pullback module functor"]
noncomputable instance RingedSpace.Module.pointPullbackFunctor_additive (x : X) :
    (RingedSpace.Module.pointPullbackFunctor x).Additive := sorry

/-- Sending a stalk module to its point module sheaf and then pushing forward along
`pointInclusion x` is the skyscraper-module functor at `x`. -/
public noncomputable def RingedSpace.Module.Skyscraper.functor
    (x : X) :
    ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) ⥤ X.Modules :=
  RingedPoint.Module.functor (X.presheaf.stalk x) ⋙ RingedSpace.Hom.pushforward (pointInclusion x)

/-- The pullback model of the module-stalk functor at `x` is left adjoint to the
skyscraper-module functor at `x`. -/
public noncomputable def RingedSpace.Module.Skyscraper.adjunction (x : X) :
    RingedSpace.Module.pointPullbackFunctor x ⊣ RingedSpace.Module.Skyscraper.functor x :=
  (SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom (pointInclusion x))).comp
    (RingedPoint.Module.equivalence (X.presheaf.stalk x)).symm.toAdjunction

/-- For a point `x : X` and a module `M` over the stalk ring at `x`,
`RingedSpace.Module.Skyscraper.atPoint x M` is the canonical pushforward along
`pointInclusion x : pointRingedSpace x ⟶ X`. -/
noncomputable def RingedSpace.Module.Skyscraper.atPoint
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    SheafOfModules.{u} ((RingedSpace.ringCatSheaf X)) :=
  (RingedSpace.Module.Skyscraper.functor x).obj M

/-- The additive group underlying a module used as the value of a skyscraper module sheaf. -/
noncomputable abbrev RingedSpace.Module.Skyscraper.value
    {X : RingedSpace.{u}} {x : X}
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) AddCommGrpCat.{u}).obj M

/-- The canonical additive map from the value module of a skyscraper module sheaf to its stalk at
an arbitrary point, obtained by taking the germ of the global section determined by that value. -/
public noncomputable def RingedSpace.Module.Skyscraper.valueToStalk
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) (x' : X) :
    RingedSpace.Module.Skyscraper.value M ⟶
      TopCat.Presheaf.stalk (RingedSpace.Module.Skyscraper.atPoint x M).val.presheaf x' :=
  (forget₂
      (ModuleCat.{u}
        ((RingedPoint.ringCatSheaf (X.presheaf.stalk x)).obj.obj
          (op (⊤ : Opens RingedPoint.carrier))))
      AddCommGrpCat.{u}).map (RingedPoint.Module.topValueIso (X.presheaf.stalk x) M).inv ≫
    TopCat.Presheaf.germ (RingedSpace.Module.Skyscraper.atPoint x M).val.presheaf ⊤ x' trivial

/-- Along a specialization `x ⤳ x'`, the value-to-stalk map is linear after restricting scalars
from `X.presheaf.stalk x` to `X.presheaf.stalk x'`. -/
theorem RingedSpace.Module.Skyscraper.valueToStalk_map_smul
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x')
    (r : X.presheaf.stalk x') (m : M) :
    RingedSpace.Module.Skyscraper.valueToStalk x M x'
        (X.presheaf.stalkSpecializes h r • m) =
      r • RingedSpace.Module.Skyscraper.valueToStalk x M x' m := sorry

/-- The value-to-stalk map bundled as a linear map over the stalk ring at a specialization of the
support point. -/
public noncomputable def RingedSpace.Module.Skyscraper.valueToStalkLinearMap
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x') :
    ((ModuleCat.restrictScalars
      (X.presheaf.stalkSpecializes h).hom).obj M) →ₗ[
        X.presheaf.stalk x']
      RingedSpace.stalkModuleCat (RingedSpace.Module.Skyscraper.atPoint x M) x' where
  toFun := RingedSpace.Module.Skyscraper.valueToStalk x M x'
  map_add' := (RingedSpace.Module.Skyscraper.valueToStalk x M x').hom.map_add
  map_smul' := RingedSpace.Module.Skyscraper.valueToStalk_map_smul x M h

/-- The canonical map from the scalar restriction of the value module to the stalk of its
skyscraper module sheaf at a specialization of the support point. -/
public noncomputable def RingedSpace.Module.Skyscraper.stalkMapOfSpecializes
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x') :
    (ModuleCat.restrictScalars
        (X.presheaf.stalkSpecializes h).hom).obj M ⟶
      RingedSpace.stalkModuleCat (RingedSpace.Module.Skyscraper.atPoint x M) x' :=
  ConcreteCategory.ofHom
    (C := ModuleCat.{u} (X.presheaf.stalk x'))
    (RingedSpace.Module.Skyscraper.valueToStalkLinearMap x M h)

/-- At a specialization of its support point, a skyscraper module sheaf has stalk canonically
isomorphic to its value module with scalars restricted along the specialization map of stalk
rings. -/
instance RingedSpace.Module.Skyscraper.stalkMapOfSpecializes_isIso
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : x ⤳ x') :
    IsIso (RingedSpace.Module.Skyscraper.stalkMapOfSpecializes x M h) := sorry

/-- Away from the specializations of its support point, the stalk of a skyscraper module sheaf is
the zero module over the ambient stalk ring. -/
theorem RingedSpace.Module.Skyscraper.stalk_isZero_of_notSpecializes
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) {x' : X} (h : ¬x ⤳ x') :
    IsZero (RingedSpace.stalkModuleCat (RingedSpace.Module.Skyscraper.atPoint x M) x') := sorry

/-- An `X.Modules` object is a skyscraper module sheaf if it is isomorphic to
`RingedSpace.Module.Skyscraper.atPoint x M` for some point `x : X` and some module `M` over the stalk ring. -/
def RingedSpace.Module.IsSkyscraper
    (ℱ : SheafOfModules.{u} ((RingedSpace.ringCatSheaf X))) : Prop :=
  ∃ (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))),
    IsIsomorphic ℱ (RingedSpace.Module.Skyscraper.atPoint x M)

end

end AlgebraicGeometry
