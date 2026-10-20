/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DiscreteFieldFibers

/-!
# Discrete field fibers of morphisms of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` has discrete
field fibers when, for every field `k` and every morphism `Spec(k) ⟶ Y`, the
space of points of the fibre product `X ×_Y Spec(k)` is discrete.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.27.5: Discrete field fibers of morphisms of algebraic spaces. -/
#check (AlgebraicGeometry.AlgebraicSpace.discreteFieldFibers :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
