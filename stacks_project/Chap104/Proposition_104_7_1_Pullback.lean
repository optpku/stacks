module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap104.Proposition_104_6_1_Pushforward

/-!
# Derived inverse image on quasi-coherent modules

A morphism of algebraic stacks induces exact inverse image `f^* = f⁻¹` of fppf
module sheaves. Restricting to `D_{LQCoh^{fbc}}` and composing with the Verdier
quotient functor `q_X` produces a functor which is left derivable along
`q_Y`, and the total left derived functor is `Lf^*_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver CategoryTheory.Functor
open CategoryTheory.Limits CategoryTheory.ObjectProperty
open DerivedCategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

open GroupoidsOver.FppfDerivedPushforwardImpl
open FppfDerivedPushforwardImpl

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- The coefficient morphism `f⁻¹ 𝒪_Y ⟶ 𝒪_X` of fppf ringed topoi is an
isomorphism, so inverse image of modules is ordinary sheaf inverse image. -/
instance fppfRingedToposHom_structureMap_isIso (f : X ⟶ Y) :
    IsIso (fppfRingedToposHom f).structureMap := sorry

/-- Underived inverse image `f^*` of fppf `𝒪`-modules along a morphism of
algebraic stacks. -/
abbrev fppfModuleInverseImage (f : X ⟶ Y) :
    fppfModules Y ⥤ fppfModules X :=
  (fppfRingedToposHom f).modulePullback

/-- `fppfModuleInverseImage` is module pullback along `fppfRingedToposHom`. -/
theorem fppfModuleInverseImage_eq (f : X ⟶ Y) :
    fppfModuleInverseImage f = (fppfRingedToposHom f).modulePullback := sorry

/-- Underived `f^*` is additive. -/
instance fppfModuleInverseImage.instAdditive (f : X ⟶ Y) :
    (fppfModuleInverseImage f).Additive :=
  RingedSite.ToposHom.modulePullback_additive (fppfRingedToposHom f)

/-- Underived `f^* = f⁻¹` preserves finite limits. -/
instance fppfModuleInverseImage.preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (fppfModuleInverseImage f) := sorry

/-- Underived `f^* = f⁻¹` preserves finite colimits. -/
instance fppfModuleInverseImage.preservesFiniteColimits (f : X ⟶ Y) :
    PreservesFiniteColimits (fppfModuleInverseImage f) := sorry

/-- Bundled exact underived inverse image along a morphism of algebraic
stacks. -/
abbrev fppfModuleInverseImageExact (f : X ⟶ Y) :
    fppfModules Y ⥤ₑ fppfModules X :=
  ExactFunctor.of (fppfModuleInverseImage f)

/-- `fppfModuleInverseImageExact` is the bundled exact functor of
`fppfModuleInverseImage`. -/
theorem fppfModuleInverseImageExact_eq (f : X ⟶ Y) :
    fppfModuleInverseImageExact f = ExactFunctor.of (fppfModuleInverseImage f) :=
  sorry

/-- Underived `f^*` sends fppf `LQCoh^{fbc}` into fppf `LQCoh^{fbc}`. -/
theorem fppfModuleInverseImage_maps_lqcohFbc (f : X ⟶ Y) :
    FppfModules.lqcohFbc Y ≤
      (FppfModules.lqcohFbc X).inverseImage (fppfModuleInverseImage f) :=
  sorry

/-- Derived inverse image `f^* : D(𝒪_Y) ⥤ D(𝒪_X)`. -/
abbrev fppfModuleDerivedInverseImage (f : X ⟶ Y) :
    ModuleDerived Y ⥤ ModuleDerived X :=
  ExactFunctor.mapDerivedCategory (fppfModuleInverseImageExact f)

/-- Derived `f^*` is `mapDerivedCategory` of the bundled exact inverse image. -/
theorem fppfModuleDerivedInverseImage_eq (f : X ⟶ Y) :
    fppfModuleDerivedInverseImage f =
      ExactFunctor.mapDerivedCategory (fppfModuleInverseImageExact f) :=
  sorry

/-- Derived `f^*` commutes with shifts. -/
instance fppfModuleDerivedInverseImage.instCommShift (f : X ⟶ Y) :
    (fppfModuleDerivedInverseImage f).CommShift ℤ := inferInstance

/-- Derived `f^*` is a triangulated functor. -/
instance fppfModuleDerivedInverseImage.instIsTriangulated (f : X ⟶ Y) :
    (fppfModuleDerivedInverseImage f).IsTriangulated := inferInstance

/-- Derived `f^*` sends `LQCoh^{fbc}` cohomology into `LQCoh^{fbc}`
cohomology. -/
theorem fppfModuleDerivedInverseImage_maps_lqcohFbc (f : X ⟶ Y) :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc Y) ≤
      (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (fppfModuleDerivedInverseImage f) := sorry

namespace DerivedLQCohFbc

/-- Restricted derived inverse image
`f^* : D_{LQCoh^{fbc}}(𝒪_Y) ⥤ D_{LQCoh^{fbc}}(𝒪_X)`. -/
abbrev inverseImage (f : X ⟶ Y) :
    DerivedLQCohFbc Y ⥤ DerivedLQCohFbc X :=
  FullSubcategory.restrict (fppfModuleDerivedInverseImage f)
    (fppfModuleDerivedInverseImage_maps_lqcohFbc f)

/-- `inverseImage` is the restriction of derived `f^*` to
`D_{LQCoh^{fbc}}`. -/
theorem inverseImage_eq (f : X ⟶ Y) :
    inverseImage f =
      FullSubcategory.restrict (fppfModuleDerivedInverseImage f)
        (fppfModuleDerivedInverseImage_maps_lqcohFbc f) := sorry

/-- The source square: restricted derived `f^*` whiskers with the inclusions
to unrestricted derived `f^*`. -/
abbrev inverseImage_comp_inclusion (f : X ⟶ Y) :
    inverseImage f ⋙ inclusion X ≅
      inclusion Y ⋙ fppfModuleDerivedInverseImage f :=
  FullSubcategory.restrict.compιIso (fppfModuleDerivedInverseImage f)
    (fppfModuleDerivedInverseImage_maps_lqcohFbc f)

/-- The source square is the inclusion comparison of restricted derived
`f^*`. -/
theorem inverseImage_comp_inclusion_eq (f : X ⟶ Y) :
    inverseImage_comp_inclusion f =
      FullSubcategory.restrict.compιIso (fppfModuleDerivedInverseImage f)
        (fppfModuleDerivedInverseImage_maps_lqcohFbc f) := sorry

/-- Restricted derived `f^*` commutes with shifts. -/
instance inverseImage.instCommShift (f : X ⟶ Y) :
    (inverseImage f).CommShift ℤ :=
  Functor.CommShift.ofComp (inverseImage_comp_inclusion f) ℤ

/-- Restricted derived `f^*` is triangulated. -/
instance inverseImage.instIsTriangulated (f : X ⟶ Y) :
    (inverseImage f).IsTriangulated := sorry

end DerivedLQCohFbc

namespace DerivedQCoh

/-- The composite `q_X ∘ f^* : D_{LQCoh^{fbc}}(𝒪_Y) ⥤ D_QCoh(𝒪_X)`. -/
abbrev pullbackToQCoh (f : X ⟶ Y) :
    DerivedLQCohFbc Y ⥤ DerivedQCoh X :=
  DerivedLQCohFbc.inverseImage f ⋙ quotientFunctor X

/-- `pullbackToQCoh` is restricted derived `f^*` followed by `q_X`. -/
theorem pullbackToQCoh_eq (f : X ⟶ Y) :
    pullbackToQCoh f =
      DerivedLQCohFbc.inverseImage f ⋙ quotientFunctor X := sorry

/-- The composite `q_X ∘ f^*` is left derivable at every object of
`D_{LQCoh^{fbc}}(𝒪_Y)` along the parasitic Verdier system. -/
instance pullbackToQCoh.everywhereDefined (f : X ⟶ Y) :
    LeftDerived.EverywhereDefined (pullbackToQCoh f) (derivedParasitic Y).trW :=
  sorry

/-- Everywhere-definedness supplies a total left derived functor of
`pullbackToQCoh` along `q_Y`. -/
instance pullbackToQCoh.hasLeftDerived (f : X ⟶ Y) :
    (pullbackToQCoh f).HasLeftDerivedFunctor (derivedParasitic Y).trW :=
  inferInstance

/-- Derived quasi-coherent inverse image
`Lf^*_QCoh : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`. -/
def pullback (f : X ⟶ Y) : DerivedQCoh Y ⥤ DerivedQCoh X :=
  (pullbackToQCoh f).totalLeftDerived (quotientFunctor Y) (derivedParasitic Y).trW

/-- `pullback` is the total left derived functor of `pullbackToQCoh` along
`q_Y`. -/
theorem pullback_eq (f : X ⟶ Y) :
    pullback f =
      (pullbackToQCoh f).totalLeftDerived (quotientFunctor Y)
        (derivedParasitic Y).trW := sorry

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

end DerivedQCoh

end AlgebraicGeometry.AlgebraicStack
