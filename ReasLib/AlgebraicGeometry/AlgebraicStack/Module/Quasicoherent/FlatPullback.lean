/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian

/-!
# Flat pullback of quasi-coherent modules

Quasi-coherent pullback along a flat morphism of algebraic stacks is exact
and preserves finite limits and finite colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [AlgebraicStack.Flat f]

/-- Quasi-coherent pullback along a flat morphism of algebraic stacks is exact. -/
theorem pullback_exact : exactFunctor (QCoh Y) (QCoh X) (pullback f) :=
  sorry

/-- Quasi-coherent pullback along a flat morphism of algebraic stacks preserves
finite limits. -/
instance pullback_preservesFiniteLimits : PreservesFiniteLimits (pullback f) :=
  (pullback_exact f).1

/-- Quasi-coherent pullback along a flat morphism of algebraic stacks preserves
finite colimits. -/
instance pullback_preservesFiniteColimits :
    PreservesFiniteColimits (pullback f) :=
  (pullback_exact f).2

end AlgebraicGeometry.GroupoidsOver.QCoh
