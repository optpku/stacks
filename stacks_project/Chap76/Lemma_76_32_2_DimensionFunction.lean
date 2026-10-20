/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.RelativeFunction

/-! Compatibility facade for the canonical public owner. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f],
    (Points B → ℤ) → Points X → ℤ)
