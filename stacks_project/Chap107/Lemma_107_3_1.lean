/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.IrreducibleComponent.Map

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.3.1 (1): if `f : U ⟶ X` is a smooth morphism from a scheme to a
locally Noetherian algebraic stack, then the closure of the image of any
irreducible component of `|U|` is an irreducible component of `|X|`. -/
@[stacks 0DR5]
#check (AlgebraicGeometry.AlgebraicStack.closure_image_mapOfSlice_mem_irreducibleComponents :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T' : irreducibleComponents U.left),
    @closure (Points X) τ (Set.image (Points.mapOfSlice f) (T' : Set U.left)) ∈
      @irreducibleComponents (Points X) τ)

/- Lemma 107.3.1 (2): if `f : U ⟶ X` is a surjective smooth morphism from a
scheme to a locally Noetherian algebraic stack, then every irreducible
component of `|X|` is the closure of the image of some irreducible component
of `|U|`. -/
@[stacks 0DR5]
#check (AlgebraicGeometry.AlgebraicStack.exists_irreducibleComponent_eq_closure_image_mapOfSlice :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (f : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ),
    ∃ T' : irreducibleComponents U.left,
      @closure (Points X) τ (Set.image (Points.mapOfSlice f) (T' : Set U.left)) =
        (T : Set (Points X)))

/- If the image of an irreducible component of `U` under `mapOfSlice f` lands in
an irreducible component `T` of `|X|`, then the closure of that image equals
`T`. -/
#check (AlgebraicGeometry.AlgebraicStack.eq_closure_image_mapOfSlice_of_subset :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U : Over S} (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T' : irreducibleComponents U.left) (T : @irreducibleComponents (Points X) τ)
    (h : Set.image (Points.mapOfSlice f) (T' : Set U.left) ⊆ (T : Set (Points X))),
    @closure (Points X) τ (Set.image (Points.mapOfSlice f) (T' : Set U.left)) =
      (T : Set (Points X)))

end AlgebraicGeometry.AlgebraicStack
