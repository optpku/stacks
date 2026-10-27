/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.EtaleFppf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Exact
public import stacks_project.Chap103.Proposition_103_8_1
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-! # Étale–fppf comparison compatibility checks

The comparison API is owned by the module and derived-category mathematical owners.
The prerequisite exports remain available to existing consumers.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty RingedSite.Hom

universe u

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImage :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    etaleModules X ⥤ fppfModules X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfHom_isFlat :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsFlat.{u} (etaleFppfHom X))

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImage.instAdditive :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    (etaleFppfInverseImage X).Additive)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageExact :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    etaleModules X ⥤ₑ fppfModules X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerived :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ModuleDerivedEtale X ⥤ ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerived.instCommShift :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerived X).CommShift ℤ)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerived.instIsTriangulated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerived X).IsTriangulated)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerived_maps_lqcohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedCategory.cohomologyIn (lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (etaleFppfInverseImageDerived X))

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbc :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedLQCohFbcEtale X ⥤ DerivedLQCohFbc X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbc_comp_inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    etaleFppfInverseImageDerivedLQCohFbc X ⋙ DerivedLQCohFbc.inclusion X ≅
      DerivedLQCohFbcEtale.inclusion X ⋙ etaleFppfInverseImageDerived X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbc.instCommShift :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedLQCohFbc X).CommShift ℤ)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbc.instIsTriangulated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedLQCohFbc X).IsTriangulated)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbc.instIsEquivalence :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedLQCohFbc X).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbc_maps_parasitic :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    derivedParasiticEtale X ≤
      (derivedParasitic X).inverseImage
        (etaleFppfInverseImageDerivedLQCohFbc X))

#check (AlgebraicGeometry.AlgebraicStack.derivedParasiticEtale_isTriangulated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    (derivedParasiticEtale X).IsTriangulated)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedParasitic :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    (derivedParasiticEtale X).FullSubcategory ⥤
      (derivedParasitic X).FullSubcategory)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedParasitic_comp_inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    etaleFppfInverseImageDerivedParasitic X ⋙ (derivedParasitic X).ι ≅
      (derivedParasiticEtale X).ι ⋙ etaleFppfInverseImageDerivedLQCohFbc X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedParasitic.instCommShift :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedParasitic X).CommShift ℤ)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedParasitic.instIsTriangulated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedParasitic X).IsTriangulated)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedParasitic.instIsEquivalence :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedParasitic X).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicStack.DerivedQCohEtale.quotientFunctor :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedLQCohFbcEtale X ⥤ DerivedQCohEtale X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbcToQCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedLQCohFbcEtale X ⥤ DerivedQCoh X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedLQCohFbcToQCoh_inverts :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (derivedParasiticEtale X).trW.IsInvertedBy
      (etaleFppfInverseImageDerivedLQCohFbcToQCoh X))

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedQCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    DerivedQCohEtale X ⥤ DerivedQCoh X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedQCoh_facIso :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    (derivedParasiticEtale X).trW.Q ⋙ etaleFppfInverseImageDerivedQCoh X ≅
      etaleFppfInverseImageDerivedLQCohFbcToQCoh X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedQCoh_fac :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X],
    (derivedParasiticEtale X).trW.Q ⋙ etaleFppfInverseImageDerivedQCoh X =
      etaleFppfInverseImageDerivedLQCohFbcToQCoh X)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedQCoh.instCommShift :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedQCoh X).CommShift ℤ)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedQCoh.instIsTriangulated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedQCoh X).IsTriangulated)

#check (AlgebraicGeometry.AlgebraicStack.etaleFppfInverseImageDerivedQCoh.instIsEquivalence :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (etaleFppfInverseImageDerivedQCoh X).IsEquivalence)
