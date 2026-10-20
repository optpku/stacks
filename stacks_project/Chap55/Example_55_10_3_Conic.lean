/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.SplitConic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- The split-conic structure morphism over its coefficient ring. -/
#check (AlgebraicGeometry.SplitConic.toSpec :
  ∀ (R : Type u) [CommRing R] (π : R),
    AlgebraicGeometry.SplitConic.model R π ⟶ Spec (CommRingCat.of R))
