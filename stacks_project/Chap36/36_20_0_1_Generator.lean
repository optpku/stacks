/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generator

universe u

#check (AlgebraicGeometry.ProjectiveSpace.beilinsonGenerator :
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules)
