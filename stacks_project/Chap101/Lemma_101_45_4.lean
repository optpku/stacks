/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.StabilizerLocus
import StacksCheckRecall

/-!
# Openness of the automorphism-group isomorphism locus

For a representable unramified morphism with proper target inertia, the
stabilizer-preserving locus is open and its inertia comparison is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.isIsoAtLocus :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Set (Points X))

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.mem_isIsoAtLocus :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {x : Points X},
    x ∈ AlgebraicStack.automorphismGroup.isIsoAtLocus f ↔
      AlgebraicStack.automorphismGroup.IsIsoAt f x)

/- Lemma 101.45.4 (1): the automorphism-group isomorphism locus of a
representable unramified morphism with proper target inertia is open. -/
@[stacks 0DUA] #check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.isOpen_isIsoAtLocus :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (h_repr : relativelyRepresentableByAlgebraicSpaces f) [Unramified f]
    [AlgebraicGeometry.AlgebraicStack.Proper (forget.{u + 1, u, u, u + 1} Y)],
    IsOpen (AlgebraicStack.automorphismGroup.isIsoAtLocus f))

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.isIsoAtOpenSubstack :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (h : IsOpen (AlgebraicStack.automorphismGroup.isIsoAtLocus f)),
    AlgebraicStack.Substack.Open X)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.pointsSet_isIsoAtOpenSubstack :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (h : IsOpen (AlgebraicStack.automorphismGroup.isIsoAtLocus f)),
    AlgebraicStack.Substack.Open.pointsSet
      (AlgebraicStack.automorphismGroup.isIsoAtOpenSubstack f h) =
      AlgebraicStack.automorphismGroup.isIsoAtLocus f)

/- Lemma 101.45.4 (2): the canonical inertia comparison over an open
substack occupying the automorphism-group isomorphism locus is an equivalence. -/
@[stacks 0DUA] #check (AlgebraicGeometry.AlgebraicStack.Inertia.comparison_isEquivalence_isIsoAtOpenSubstack :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (h_repr : relativelyRepresentableByAlgebraicSpaces f) [Unramified f]
    [AlgebraicGeometry.AlgebraicStack.Proper (forget.{u + 1, u, u, u + 1} Y)]
    (U : AlgebraicStack.Substack.Open X)
    (hU : AlgebraicStack.Substack.Open.pointsSet U =
      AlgebraicStack.automorphismGroup.isIsoAtLocus f),
    (toBasedFunctor (AlgebraicStack.Inertia.comparison
      (AlgebraicStack.Substack.Open.inclusion U ≫ f))).IsEquivalence)

