/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

/-!
# Finite locally free cohomology on an open subspace

The predicate in this file is the canonical restriction-based formulation of saying that all
cohomology sheaves of a derived module are finite locally free on an open subspace.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

variable {X : RingedSpace.{u}}

/-- Every cohomology sheaf of `E` becomes finite locally free after restriction to `U`. -/
abbrev finiteLocallyFreeOn (E : ModuleDerived X) (U : Opens X.carrier) : Prop :=
  DerivedCategory.cohomologyIn
    (SheafOfModules.IsFiniteLocallyFree :
      ObjectProperty (RingedSpace.Modules (X.restrict U.isOpenEmbedding)))
    ((moduleRestrictionToOpenDerived X U).obj E)

/-- Finite local freeness on an open subspace is a degreewise cohomology condition. -/
theorem finiteLocallyFreeOn_iff (E : ModuleDerived X) (U : Opens X.carrier) :
    finiteLocallyFreeOn E U ↔
      ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree
        ((DerivedCategory.homologyFunctor
          (RingedSpace.Modules (X.restrict U.isOpenEmbedding)) i).obj
            ((moduleRestrictionToOpenDerived X U).obj E)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
