/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
public import ReasLib.CategoryTheory.Sites.PrecoverageSite

/-! # Precoverages on slice sites -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The slice precoverage associated to a Grothendieck topology is a site when `C` has
fibre products. -/
theorem over_toPrecoverage_isSite (X : C) [HasPullbacks C] :
    (J.over X).toPrecoverage.IsSite :=
  sorry

/-- Postcomposition `Over.map f` has the selected-cover lifting property for the induced slice precoverages. -/
theorem overMap_hasCoverLifts {X Y : C} (f : X ⟶ Y) [HasPullbacks C] :
    Functor.Precoverage.HasCoverLifts (Over.map f)
      (J.over X).toPrecoverage (J.over Y).toPrecoverage :=
  sorry

end CategoryTheory.GrothendieckTopology

