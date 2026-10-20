/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison

/-! Compatibility facade for the canonical scheme/quasi-coherent module comparison. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.restrictToScheme :
  ∀ {S : Scheme.{u}} (U : Over S), QCoh (ofOver U) ⥤ Scheme.QCoh U.left)
