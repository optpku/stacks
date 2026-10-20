/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat morphisms in slices under base change

This file records preservation of flat morphisms by the canonical pullback
functor between slice categories of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/-- A flat morphism in a slice remains flat after applying the canonical pullback functor. -/
instance instOverPullbackMap {S S' : Scheme.{u}} (g : S' ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) [Flat f.left] :
    Flat ((Over.pullback g).map f).left :=
  MorphismProperty.overPullbackMap (P := @Flat) g f inferInstance

end AlgebraicGeometry.Flat
