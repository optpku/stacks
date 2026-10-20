/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Monomorphism
import StacksCheckRecall

/-!
# Monomorphisms and immersions of algebraic stacks are separated and DM

A monomorphism of algebraic stacks is separated and DM, and the same holds
for immersions of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.4.15: Monomorphisms and immersions of algebraic stacks are
separated and DM. -/
@[stacks 06MY] #check (AlgebraicGeometry.AlgebraicStack.Separated.of_mono :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Mono f], AlgebraicGeometry.AlgebraicStack.Separated f)

#check (AlgebraicGeometry.AlgebraicStack.Separated.of_immersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Immersion f], AlgebraicGeometry.AlgebraicStack.Separated f)

#check (AlgebraicGeometry.AlgebraicStack.DM.of_mono :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Mono f], AlgebraicGeometry.AlgebraicStack.DM f)

#check (AlgebraicGeometry.AlgebraicStack.DM.of_immersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Immersion f], AlgebraicGeometry.AlgebraicStack.DM f)
