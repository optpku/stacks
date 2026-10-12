/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable (X : Scheme.{u})

#check
  (CategoryTheory.DerivedCategory.CohomologyIn.triangulated
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :
    (CategoryTheory.DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).IsTriangulated)

end AlgebraicGeometry.Scheme.DerivedQCoh
