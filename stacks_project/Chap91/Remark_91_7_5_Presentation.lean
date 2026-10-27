/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Presentation

/-!
# Lifted polynomial presentations of square-zero extensions

The coefficient map and polynomial-presentation constructions are provided by the
mathematical owner imported here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open TopologicalSpace
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S X : RingedSpace.{u}} {f : X ⟶ S} {G : X.Modules}

#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.structureMap :
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) →
      (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf ⟶
        inverseImageX' sol)

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
