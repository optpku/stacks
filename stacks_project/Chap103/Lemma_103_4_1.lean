/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FlatPullback
import StacksCheckRecall

/-!
# Pullback of quasi-coherent modules along a flat morphism

If `f : X ⟶ Y` is a flat morphism of algebraic stacks, then quasi-coherent
pullback `f^* : QCoh Y ⥤ QCoh X` is an exact functor.
-/

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 103.4.1: if `f : X ⟶ Y` is a flat morphism of algebraic stacks, then
the quasi-coherent pullback `f^* : QCoh Y ⥤ QCoh X` is an exact functor. -/
@[stacks 076X] #check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_exact :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.Flat f],
    exactFunctor (QCoh Y) (QCoh X) (QCoh.pullback f))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_preservesFiniteLimits :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.Flat f],
    PreservesFiniteLimits (QCoh.pullback f))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_preservesFiniteColimits :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.Flat f],
    PreservesFiniteColimits (QCoh.pullback f))
