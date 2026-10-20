/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.ClosedImmersion.QuasiCompact
import StacksCheckRecall

/-!
# Closed immersions of algebraic stacks are quasi-compact

A closed immersion of algebraic stacks is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.7.5: A closed immersion of algebraic stacks is quasi-compact. -/
@[stacks 0CL1] #check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.quasiCompact :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.ClosedImmersion f],
    AlgebraicGeometry.AlgebraicStack.QuasiCompact f)
