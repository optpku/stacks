/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The category of finitely presented flat modules with proper support on scheme-valued fibers. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.category :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    [FinitePresentation f] → CategoryTheory.Cat.{u + 1, u + 1})
