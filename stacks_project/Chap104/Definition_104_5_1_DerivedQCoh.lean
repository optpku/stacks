/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent

/-!
# Derived quasi-coherent modules

Typed compatibility checks for the fppf derived quotient and the distinct étale
construction, with the module prerequisite exports retained.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.fppfModulesHasDerivedCategory :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    HasDerivedCategory (fppfModules X))

#check (AlgebraicGeometry.AlgebraicStack.ModuleDerived :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    DerivedLQCohFbc X ⥤ ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicStack.derivedParasitic :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (DerivedLQCohFbc X))

#check (AlgebraicGeometry.AlgebraicStack.derivedParasitic_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (E : DerivedLQCohFbc X),
    derivedParasitic X E ↔
      ∀ n : ℤ, FppfModules.parasitic X
        ((DerivedCategory.homologyFunctor (fppfModules X) n).obj
          ((DerivedLQCohFbc.inclusion X).obj E)))

#check (AlgebraicGeometry.AlgebraicStack.derivedParasitic_eq_intersection :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    derivedParasitic X =
      (DerivedCategory.cohomologyIn (FppfModules.parasiticLQCohFbc X)).inverseImage
        (DerivedLQCohFbc.inclusion X))

#check (AlgebraicGeometry.AlgebraicStack.derivedParasitic_isTriangulated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (derivedParasitic X).IsTriangulated)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.quotientFunctor :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    DerivedLQCohFbc X ⥤ DerivedQCoh X)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    DerivedQCoh X =
      ObjectProperty.verdierQuotient
        ((DerivedCategory.cohomologyIn (FppfModules.parasiticLQCohFbc X)).inverseImage
          (DerivedLQCohFbc.inclusion X)))

#check (AlgebraicGeometry.AlgebraicStack.etaleModulesHasDerivedCategory :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    HasDerivedCategory (etaleModules X))

#check (AlgebraicGeometry.AlgebraicStack.ModuleDerivedEtale :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbcEtale :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbcEtale.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    DerivedLQCohFbcEtale X ⥤ ModuleDerivedEtale X)

#check (AlgebraicGeometry.AlgebraicStack.derivedParasiticEtale :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (DerivedLQCohFbcEtale X))

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCohEtale :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    Type (u + 1))

end AlgebraicGeometry.AlgebraicStack
