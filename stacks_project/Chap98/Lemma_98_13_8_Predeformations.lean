/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FiniteDimensionalPredeformations

/-! # Finite-dimensional tangent and infinitesimal automorphism spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupoidsOver.HasFiniteDimensionalPredeformations :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S], GroupoidsOver S → Prop)
