/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

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

/-- The projection of a category fibred in groupoids is continuous for the inherited fppf
topology. -/
instance projection_isContinuous (X : GroupoidsOver S) :
    X.p.IsContinuous (inheritedFppfTopology X) (Scheme.fppfTopology.over S) :=
  Functor.inheritedTopology.isContinuous X.p (Scheme.fppfTopology.over S)

/-- A 1-morphism of categories fibred in groupoids is continuous for the inherited fppf
topologies. -/
instance toFunctor_isContinuous (f : X ⟶ Y) :
    (toCartesianBasedFunctor f).toBasedFunctor.IsContinuous
      (inheritedFppfTopology X) (inheritedFppfTopology Y) :=
  CartesianBasedFunctor.inheritedTopology.isContinuous (toCartesianBasedFunctor f)
    (Scheme.fppfTopology.over S)

/-- Inverse image of the structure sheaf of `Y` along a 1-morphism `f : X ⟶ Y`. -/
def inverseImageStructureSheaf (f : X ⟶ Y) :
    Sheaf (inheritedFppfTopology X) RingCat.{u} :=
  ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous RingCat.{u}
      (inheritedFppfTopology X) (inheritedFppfTopology Y)).obj
    (structureSheaf Y)

/-- The canonical identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` for a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. -/
def structureSheafIso (f : X ⟶ Y) :
    inverseImageStructureSheaf f ≅ structureSheaf X :=
  (Functor.sheafPushforwardContinuousComp'
      (eqToIso (toCartesianBasedFunctor f).toBasedFunctor.w :
        (toCartesianBasedFunctor f).toFunctor ⋙ Y.p ≅ X.p)
      RingCat.{u} (inheritedFppfTopology X) (inheritedFppfTopology Y)
      (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` obtained from `structureSheafIso`. -/
def structureSheafMap (f : X ⟶ Y) :
    structureSheaf X ⟶ inverseImageStructureSheaf f :=
  (structureSheafIso f).inv

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` is an isomorphism, so `f^* = f⁻¹`. -/
theorem structureSheafMap_isIso (f : X ⟶ Y) :
    IsIso (structureSheafMap f) :=
  sorry

/-- The pullback functor `f^* = f⁻¹ : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of sheaves of modules. -/
def modulePullback (f : X ⟶ Y) :
    SheafOfModules.{u} (structureSheaf Y) ⥤ SheafOfModules.{u} (structureSheaf X) :=
  SheafOfModules.pushforward (structureSheafMap f)

/-- `modulePullback f` is module inverse image along `structureSheafMap f`. -/
theorem modulePullback_eq (f : X ⟶ Y) :
    modulePullback f = SheafOfModules.pushforward (structureSheafMap f) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
