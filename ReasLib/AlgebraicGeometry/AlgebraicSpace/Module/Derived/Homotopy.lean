/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward

/-! # Homotopy models for derived module functors

These definitions fix the original coefficient universe and the canonical Abelian
structures used to compare module functors with their total right-derived functors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The homotopy category of complexes of module sheaves on an algebraic space. -/
abbrev modulesHomotopy (X : AlgebraicSpace S) :=
  @HomotopyCategory ℤ X.Modules _ X.modulesAbelian.toPreadditive (up ℤ)

/-- The localization from the module homotopy category to the derived category. -/
abbrev modulesQh (X : AlgebraicSpace S) :
    modulesHomotopy X ⥤ ModuleDerived X :=
  @DerivedCategory.Qh X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)

/-- The additive functor induced on module homotopy categories. -/
abbrev modulesMapHomotopy {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    modulesHomotopy X ⥤ modulesHomotopy Y :=
  @mapHomotopyCategory ℤ X.Modules _ X.modulesAbelian.toPreadditive
    Y.Modules _ Y.modulesAbelian.toPreadditive F inferInstance (up ℤ)

/-- The homotopy-to-derived functor associated to an additive module functor. -/
abbrev modulesHomotopyToDerived {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    modulesHomotopy X ⥤ ModuleDerived Y :=
  @Homotopy.toDerived X.Modules _ X.modulesAbelian.toPreadditive
    Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y) F inferInstance

/-- The K-injective total right-derived functor of an additive module functor. -/
abbrev modulesHomotopyFunctor {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  @RightDerived.KInjective.functor.{u} X.Modules _ X.modulesAbelian
    Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory X)
    (modulesHasDerivedCategory Y) F inferInstance
    (inferInstance : IsGrothendieckAbelian.{u} X.Modules) inferInstance

/-- The homotopy-level unit for the K-injective derived module functor. -/
abbrev modulesHomotopyUnit {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    modulesHomotopyToDerived F ⟶ modulesQh X ⋙ modulesHomotopyFunctor F :=
  @RightDerived.Homotopy.unit X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)
    Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y) F inferInstance inferInstance

/-- The homotopy-level unit for exact étale restriction. -/
abbrev modulesRestrictFactorshInv {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    modulesHomotopyToDerived (restrictFunctor f) ⟶
      modulesQh Y ⋙ restrictFunctorDerived f :=
  (@mapDerivedCategoryFactorsh Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y)
    X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)
    (restrictFunctor f) inferInstance inferInstance inferInstance).inv

end AlgebraicGeometry.AlgebraicSpace.Modules

