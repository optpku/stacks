/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.FreeDimensional

universe u

/- 97.13.0.2: The groupoid of distinguished finite free algebras over a ring. -/
#check
  (@AlgebraicGeometry.FreeDimAlgebra : ∀ (R : Type u) [CommRing R] (d : ℕ) [NeZero d], CategoryTheory.Grpd.{u, u})
