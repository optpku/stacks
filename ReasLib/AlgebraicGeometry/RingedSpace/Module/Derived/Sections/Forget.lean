/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived forgetting of section-module structure

This file owns the exact forgetful functor from modules over the ring of sections on an open
subset to additive groups, together with its bounded-below and unbounded derived actions.  It is
the common dependency of Cech-source and derived-sections-target comparisons.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections

/-- The canonical forgetful functor from modules over `Γ(U, 𝒪_X)` to additive groups. -/
@[stacks 0D6J "forget the section-module structure"]
abbrev forgetFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ModuleCat (sectionsRingOnOpen X U) ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}

/-- Forgetting the module structure over `Γ(U, 𝒪_X)` as a bundled exact functor. -/
@[stacks 0D6J "exact section-module forgetful functor"]
abbrev exactForget (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ModuleCat (sectionsRingOnOpen X U) ⥤ₑ AddCommGrpCat.{u} :=
  ExactFunctor.of (forgetFunctor X U)

/-- The direct exact action of section-module forgetting on bounded-below derived categories. -/
@[stacks 0D6J "exact derived section-module forgetting"]
abbrev exactDerivedForget (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory.Plus (ModuleCat (sectionsRingOnOpen X U)) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  ExactFunctor.Derived.Plus.functor (exactForget X U)

/-- The common unbounded codomain functor obtained by including a bounded-below module complex
and then forgetting its section-module structure. -/
@[stacks 0D6J "underlying unbounded derived section modules"]
abbrev underlyingDerivedFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory.Plus (ModuleCat (sectionsRingOnOpen X U)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  DerivedCategory.Plus.ι ⋙ (forgetFunctor X U).mapDerivedCategory

/-- The exact bounded-below action followed by inclusion is canonically the common unbounded
derived forgetful functor. -/
@[stacks 0D6J "bounded and unbounded derived forgetting comparison"]
noncomputable def exactDerivedForgetCompιIso
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    exactDerivedForget X U ⋙ DerivedCategory.Plus.ι ≅
      underlyingDerivedFunctor X U :=
  ExactFunctor.Derived.Plus.compιIso (exactForget X U)

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections
