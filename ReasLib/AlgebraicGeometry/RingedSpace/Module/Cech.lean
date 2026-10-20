/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf

/-!
# Čech cohomology of module sheaves on a ringed space

The construction is factored through the underlying additive presheaf, making
both the Čech complex and its degreewise homology functor available to later
applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The additive Čech complex of an `𝒪_X`-module for a family of opens. -/
abbrev moduleCechComplex
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : X.Modules) :
    HomologicalComplex AddCommGrpCat.{u} (ComplexShape.up ℕ) :=
  (cechComplexFunctor 𝒰).obj ((moduleUnderlyingPresheaf X).obj ℱ)

/-- The functor sending an `𝒪_X`-module to its additive Čech complex for a
fixed family of opens. -/
abbrev moduleCechComplexFunctor
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier) :
    X.Modules ⥤ HomologicalComplex AddCommGrpCat.{u} (ComplexShape.up ℕ) :=
  moduleUnderlyingPresheaf X ⋙ cechComplexFunctor 𝒰

/-- The degree-`p` Čech cohomology functor of `𝒪_X`-modules for a fixed family
of opens. -/
abbrev moduleCechCohomologyFunctor
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier) (p : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  moduleCechComplexFunctor 𝒰 ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p

/-- The degree-`p` Čech cohomology group of an `𝒪_X`-module with respect to a
family of opens `𝒰`. -/
abbrev moduleCechCohomology
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : X.Modules) (p : ℕ) : AddCommGrpCat.{u} :=
  (moduleCechCohomologyFunctor 𝒰 p).obj ℱ

/-- The Čech-complex functor evaluated at a module is the corresponding
objectwise Čech complex. -/
@[simp]
theorem moduleCechComplexFunctor_obj
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : X.Modules) :
    (moduleCechComplexFunctor 𝒰).obj ℱ = moduleCechComplex 𝒰 ℱ := sorry

/-- The degree-`p` Čech-cohomology functor evaluated at a module is the
corresponding objectwise Čech cohomology group. -/
@[simp]
theorem moduleCechCohomologyFunctor_obj
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : X.Modules) (p : ℕ) :
    (moduleCechCohomologyFunctor 𝒰 p).obj ℱ = moduleCechCohomology 𝒰 ℱ p := sorry

end AlgebraicGeometry.RingedSpace
