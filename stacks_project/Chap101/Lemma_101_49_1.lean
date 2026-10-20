/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Kolmogorov
import StacksCheckRecall

/-!
# Kolmogorov points of decent algebraic stacks

The points space of a decent algebraic stack is Kolmogorov in the sense of
Topology, Definition 5.8.6, i.e. a `T0Space` in every canonical
`IsPointsTopology`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.49.1: The space of points of a decent algebraic stack is Kolmogorov. -/
@[stacks 0GW7] #check (AlgebraicGeometry.AlgebraicStack.IsDecent.t0Space :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X]
    (τ : TopologicalSpace (Points X)), IsPointsTopology X τ → @T0Space (Points X) τ)

#check (AlgebraicGeometry.AlgebraicStack.IsDecent.eq_of_specializes_specializes :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
    {τ : TopologicalSpace (Points X)}, IsPointsTopology X τ →
    ∀ {x x' : Points X}, @Specializes (Points X) τ x x' →
      @Specializes (Points X) τ x' x → x = x')
