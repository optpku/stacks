/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf

/-!
# Pullback of modules on categories fibred in groupoids

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces the inverse image
`f⁻¹` of sheaves of modules. Because `f⁻¹ 𝒪_Y ≅ 𝒪_X`, this agrees with `f^*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Inverse image of the structure sheaf of `Y` along a 1-morphism `f : X ⟶ Y`. -/
def inverseImageStructureSheaf (f : X ⟶ Y) :
    Sheaf (fppfTopology X) RingCat.{u} :=
  ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous RingCat.{u}
      (fppfTopology X) (fppfTopology Y)).obj
    (structureSheaf Y)

/-- The canonical identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` for a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. -/
def structureSheafIso (f : X ⟶ Y) :
    inverseImageStructureSheaf f ≅ structureSheaf X :=
  (Functor.sheafPushforwardContinuousComp'
      (eqToIso (toCartesianBasedFunctor f).toBasedFunctor.w :
        (toCartesianBasedFunctor f).toFunctor ⋙ Y.p ≅ X.p)
      RingCat.{u} (fppfTopology X) (fppfTopology Y)
      (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` obtained from `structureSheafIso`. -/
def structureSheafMap (f : X ⟶ Y) :
    structureSheaf X ⟶ inverseImageStructureSheaf f :=
  (structureSheafIso f).inv

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` is an isomorphism, so `f^* = f⁻¹`. -/
instance structureSheafMap_isIso (f : X ⟶ Y) :
    IsIso (structureSheafMap f) :=
  (structureSheafIso f).isIso_inv

/-- The pullback functor `f^* = f⁻¹ : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of sheaves of modules. -/
def modulePullback (f : X ⟶ Y) :
    SheafOfModules.{u} (structureSheaf Y) ⥤ SheafOfModules.{u} (structureSheaf X) :=
  SheafOfModules.pushforward (structureSheafMap f)

/-- `modulePullback f` is module inverse image along `structureSheafMap f`. -/
theorem modulePullback_eq (f : X ⟶ Y) :
    modulePullback f = SheafOfModules.pushforward (structureSheafMap f) :=
  rfl

end AlgebraicGeometry.GroupoidsOver
