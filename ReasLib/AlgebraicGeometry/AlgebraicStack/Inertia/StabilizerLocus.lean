/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Comparison.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia

/-!
# The stabilizer-preserving locus

For a representable unramified morphism with proper target inertia, the locus
where automorphism groups are preserved is open, and the inertia comparison
over its corresponding open substack is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.automorphismGroup

/-- The set of points where a morphism induces an isomorphism of automorphism groups. -/
def isIsoAtLocus {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) : Set (Points X) :=
  {x | IsIsoAt f x}

/-- Membership in the automorphism-group isomorphism locus is the pointwise
automorphism-group isomorphism condition. -/
theorem mem_isIsoAtLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {x : Points X} :
    x ∈ isIsoAtLocus f ↔ IsIsoAt f x := sorry

/-- For a representable unramified morphism of algebraic stacks with proper
target inertia projection, the automorphism-group isomorphism locus is open. -/
@[stacks 0DUA]
theorem isOpen_isIsoAtLocus {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f) [Unramified f]
    [AlgebraicGeometry.AlgebraicStack.Proper (forget.{u + 1, u, u, u + 1} Y)] :
    IsOpen (isIsoAtLocus f) := sorry

/-- The open substack defined by the automorphism-group isomorphism locus
and a certificate that this locus is open. -/
def isIsoAtOpenSubstack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : IsOpen (isIsoAtLocus f)) : Substack.Open X :=
  Substack.Open.ofOpens (Opens.mk (isIsoAtLocus f) h)

/-- The point image of the open substack defined by the automorphism-group
isomorphism locus is exactly that locus. -/
theorem pointsSet_isIsoAtOpenSubstack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : IsOpen (isIsoAtLocus f)) :
    Substack.Open.pointsSet (isIsoAtOpenSubstack f h) = isIsoAtLocus f := sorry

end AlgebraicGeometry.AlgebraicStack.automorphismGroup

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- For a representable unramified morphism with proper target inertia
projection, the canonical inertia comparison over an open substack whose
point image is the automorphism-group isomorphism locus is an equivalence. -/
@[stacks 0DUA]
theorem comparison_isEquivalence_isIsoAtOpenSubstack {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h_repr : relativelyRepresentableByAlgebraicSpaces f) [Unramified f]
    [AlgebraicGeometry.AlgebraicStack.Proper (forget.{u + 1, u, u, u + 1} Y)]
    (U : Substack.Open X)
    (hU : Substack.Open.pointsSet U = automorphismGroup.isIsoAtLocus f) :
    (toBasedFunctor (comparison (Substack.Open.inclusion U ≫ f))).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
