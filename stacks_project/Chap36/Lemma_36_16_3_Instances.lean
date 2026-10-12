/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open CategoryTheory

universe u

variable (X : AlgebraicGeometry.Scheme.{u})

#check (CategoryTheory.DerivedCategory.CohomologyIn.stableUnderShift
  (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :
    (AlgebraicGeometry.Scheme.ModuleDerived.quasicoherentProperty X).IsStableUnderShift ℤ)
