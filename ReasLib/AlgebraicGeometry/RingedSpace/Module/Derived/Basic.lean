/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk

/-!
# Derived categories of modules on ringed spaces

This file supplies the canonical homology and derived-category instances for sheaves of modules
on an arbitrary ringed space.  It is independent of the Chapter 20 cohomology applications.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The canonical homology structure on `RingedSpace.Modules X`, induced by its abelian
structure. -/
instance ringedSpaceModules_categoryWithHomology
    (X : RingedSpace.{u}) :
    CategoryWithHomology (RingedSpace.Modules X) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- The standard derived-category structure on `RingedSpace.Modules X`. -/
instance ringedSpaceModules_hasDerivedCategory
    (X : RingedSpace.{u}) [CategoryWithHomology (RingedSpace.Modules X)] :
    HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

/-- The unbounded derived category `D(𝒪_X)` of module sheaves on a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory X.Modules

end AlgebraicGeometry.RingedSpace

