/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.EndomorphismAlgebra

universe u

#check (AlgebraicGeometry.ProjectiveSpace.Beilinson.toEnd_bijective :
  ∀ (A : Type u) [CommRing A] (n : ℕ),
    Function.Bijective (AlgebraicGeometry.ProjectiveSpace.Beilinson.toEnd A n))
