/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FreeDimensionalAlgebra

universe u

/- 97.13.0.2: The presheaf of distinguished finite free algebra groupoids on schemes. -/
#check
  (@AlgebraicGeometry.FA : ∀ (d : ℕ) [NeZero d],
    CategoryTheory.Functor (AlgebraicGeometry.Scheme.{u})ᵒᵖ CategoryTheory.Grpd.{u, u})
