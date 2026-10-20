/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- The relative finite-presentation API is provided by its reusable mathematical owner. -/
#check
  (AlgebraicGeometry.Scheme.Modules.finitePresentationOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f], ObjectProperty X.Modules)
