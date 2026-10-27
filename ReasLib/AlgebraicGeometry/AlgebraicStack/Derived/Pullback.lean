/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Limits DerivedCategory DerivedCategory.TStructure
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

/-- Underived `f^*` is additive. -/
instance fppfModuleInverseImage.instAdditive (f : X ⟶ Y) :
    (fppfModuleInverseImage f).Additive := sorry

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

/-- Derived inverse image `f^* : D(𝒪_Y) ⥤ D(𝒪_X)`. -/
abbrev fppfModuleDerivedInverseImage (f : X ⟶ Y) :
    ModuleDerived Y ⥤ ModuleDerived X :=
  ExactFunctor.mapDerivedCategory (fppfModuleInverseImageExact f)

/-- Derived `f^*` commutes with shifts. -/
instance fppfModuleDerivedInverseImage.instCommShift (f : X ⟶ Y) :
    (fppfModuleDerivedInverseImage f).CommShift ℤ := inferInstance

/-- Derived `f^*` is a triangulated functor. -/
instance fppfModuleDerivedInverseImage.instIsTriangulated (f : X ⟶ Y) :
    (fppfModuleDerivedInverseImage f).IsTriangulated := inferInstance

end AlgebraicGeometry.AlgebraicStack
