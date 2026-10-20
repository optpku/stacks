/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IdealPower.Generation

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

/- The ideal-power product inclusion remains available to filtration consumers. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.productInclusion :
  ∀ {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    {m n : ℕ}, m ≤ n →
      ((AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.product I f F n :
        X.Modules) ⟶
      (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.product I f F m :
        X.Modules)))
