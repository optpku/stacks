/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pullback
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.Saturation
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open DerivedCategory DerivedCategory.TStructure
open scoped Bicategory

noncomputable section

universe u

-- Local instance justification (defeq pin): the homotopy localization must use the Abelian and induced additive structures of the fppf module presentation in ModuleDerived.
attribute [local instance 2000] GroupoidsOver.fppfModulesAbelian
  Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms fppfModulesHasDerivedCategory

-- Local instance justification (defeq pin): ModuleDerived uses this standard localization through fppfModulesHasDerivedCategory, at the same module-category universe.
attribute [local instance 1900] HasDerivedCategory.standard


namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]

/-- Underived `f^*` sends fppf `LQCoh^{fbc}` into fppf `LQCoh^{fbc}`. -/
theorem fppfModuleInverseImage_maps_lqcohFbc (f : X ⟶ Y) :
    FppfModules.lqcohFbc Y ≤
      (FppfModules.lqcohFbc X).inverseImage (fppfModuleInverseImage f) := sorry

/-- Derived `f^*` sends `LQCoh^{fbc}` cohomology into `LQCoh^{fbc}`
cohomology. -/
theorem fppfModuleDerivedInverseImage_maps_lqcohFbc (f : X ⟶ Y) :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y) ≤
      (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (fppfModuleDerivedInverseImage f) := sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]

/-- Restricted derived inverse image
`f^* : D_{LQCoh^{fbc}}(𝒪_Y) ⥤ D_{LQCoh^{fbc}}(𝒪_X)`. -/
abbrev inverseImage (f : X ⟶ Y) :
    DerivedLQCohFbc Y ⥤ DerivedLQCohFbc X :=
  FullSubcategory.restrict (fppfModuleDerivedInverseImage f)
    (fppfModuleDerivedInverseImage_maps_lqcohFbc f)

/-- The inclusion comparison: restricted derived `f^*` whiskers with the inclusions
to unrestricted derived `f^*`. -/
abbrev inverseImage_comp_inclusion (f : X ⟶ Y) :
    inverseImage f ⋙ inclusion X ≅
      inclusion Y ⋙ fppfModuleDerivedInverseImage f :=
  FullSubcategory.restrict.compιIso (fppfModuleDerivedInverseImage f)
    (fppfModuleDerivedInverseImage_maps_lqcohFbc f)

/-- Restricted derived `f^*` commutes with shifts. -/
instance inverseImage.instCommShift (f : X ⟶ Y) :
    (inverseImage f).CommShift ℤ :=
  Functor.CommShift.ofComp (inverseImage_comp_inclusion f) ℤ

/-- Restricted derived `f^*` is triangulated. -/
instance inverseImage.instIsTriangulated (f : X ⟶ Y) :
    (inverseImage f).IsTriangulated := sorry

end AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc

namespace AlgebraicGeometry.AlgebraicStack.DerivedQCoh

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]

/-- The composite `q_X ∘ f^* : D_{LQCoh^{fbc}}(𝒪_Y) ⥤ D_QCoh(𝒪_X)`. -/
abbrev pullbackToQCoh (f : X ⟶ Y) :
    DerivedLQCohFbc Y ⥤ DerivedQCoh X :=
  DerivedLQCohFbc.inverseImage f ⋙ quotientFunctor X

/-- The composite `q_X ∘ f^*` is left derivable at every object of
`D_{LQCoh^{fbc}}(𝒪_Y)` along the parasitic Verdier system. -/
instance pullbackToQCoh.everywhereDefined (f : X ⟶ Y) :
    LeftDerived.EverywhereDefined (pullbackToQCoh f) (derivedParasitic Y).trW := sorry

/-- Everywhere-definedness supplies a total left derived functor of
`pullbackToQCoh` along `q_Y`. -/
instance pullbackToQCoh.hasLeftDerived (f : X ⟶ Y) :
    (pullbackToQCoh f).HasLeftDerivedFunctor (derivedParasitic Y).trW :=
  inferInstance

/-- Derived quasi-coherent inverse image
`Lf^*_QCoh : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`. -/
def pullback (f : X ⟶ Y) : DerivedQCoh Y ⥤ DerivedQCoh X :=
  (pullbackToQCoh f).totalLeftDerived (quotientFunctor Y) (derivedParasitic Y).trW

/-- `Lf^*_QCoh` commutes with shifts. -/
instance pullback.instCommShift (f : X ⟶ Y) :
    (pullback f).CommShift ℤ :=
  Functor.totalLeftDerived_commShift (pullbackToQCoh f)
    (derivedParasitic Y).trW (quotientFunctor Y)

/-- `Lf^*_QCoh` is triangulated. -/
instance pullback.instIsTriangulated (f : X ⟶ Y) :
    (pullback f).IsTriangulated :=
  Functor.totalLeftDerived_isTriangulated (pullbackToQCoh f)
    (derivedParasitic Y).trW (quotientFunctor Y)

end AlgebraicGeometry.AlgebraicStack.DerivedQCoh
