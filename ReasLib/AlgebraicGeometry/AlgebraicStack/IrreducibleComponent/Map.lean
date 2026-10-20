/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Under a smooth morphism from a scheme to a locally Noetherian algebraic stack,
the closure of the image of every irreducible component of the scheme is an
irreducible component of the stack's canonical point space. -/
theorem closure_image_mapOfSlice_mem_irreducibleComponents
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T' : irreducibleComponents U.left) :
    @closure (Points X) τ (Set.image (Points.mapOfSlice f) (T' : Set U.left)) ∈
      @irreducibleComponents (Points X) τ :=
  sorry

/-- Under a surjective smooth morphism from a scheme to a locally Noetherian
algebraic stack, every irreducible component of the stack's canonical point space
is the closure of the image of an irreducible component of the scheme. -/
theorem exists_irreducibleComponent_eq_closure_image_mapOfSlice
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (f : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ) :
    ∃ T' : irreducibleComponents U.left,
      @closure (Points X) τ (Set.image (Points.mapOfSlice f) (T' : Set U.left)) =
        (T : Set (Points X)) :=
  sorry

/-- Under a smooth morphism from a scheme to a locally Noetherian algebraic stack,
if the image of a source irreducible component is contained in a target irreducible
component, then the closure of that image equals the target component. -/
theorem eq_closure_image_mapOfSlice_of_subset
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T' : irreducibleComponents U.left) (T : @irreducibleComponents (Points X) τ)
    (h : Set.image (Points.mapOfSlice f) (T' : Set U.left) ⊆ (T : Set (Points X))) :
    @closure (Points X) τ (Set.image (Points.mapOfSlice f) (T' : Set U.left)) =
      (T : Set (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
