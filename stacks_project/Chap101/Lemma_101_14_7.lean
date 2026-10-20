/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective.LocalAtTarget
import StacksCheckRecall

/-!
# Affine characterizations of universally injective morphisms of algebraic stacks

Lemma 101.14.7 records that a morphism of algebraic stacks is universally
injective iff this is tested by universally injective projections after
affine-scheme-valued base change.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.14.7: for a morphism `f : X ⟶ Y` of algebraic stacks, the following
are equivalent: `UniversallyInjective f`; and for every affine scheme `Z` and
morphism `Z ⟶ Y` the projection `Z ×_Y X ⟶ Z` is universally injective.
The official source lists a third enumerated item `add more here`, which is an
editorial stub and is omitted. -/
@[stacks 0DTN] #check
  (AlgebraicGeometry.AlgebraicStack.UniversallyInjective.iff_forallAffine :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y), AlgebraicGeometry.AlgebraicStack.UniversallyInjective f ↔
        AlgebraicGeometry.AlgebraicStack.UniversallyInjective.forallAffine f)
