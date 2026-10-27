/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Factorization
import StacksCheckRecall

/-!
# Factorization through residual gerbes

A morphism from a reduced algebraic stack whose image on points is contained in
`{x}` factors through the residual gerbe at `x` when the target is decent or
locally Noetherian and its canonical inertia projection is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open Groupoids.Hom
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

/- Lemma 101.51.2: A reduced-source morphism whose point-image is contained in
`{x}` factors through a residual gerbe at `x` when the target is decent or locally
Noetherian and its canonical inertia projection is quasi-compact. -/
@[stacks 0H25] #check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factorsThrough_of_range_subset_singleton :
    ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}),
    FactorsThrough f ι)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factorsThrough_of_isDecent :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsDecent X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}),
    FactorsThrough f ι)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factorsThrough_of_isLocallyNoetherian :
    ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}),
    FactorsThrough f ι)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factorsThrough_residualGerbeι :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X}
    (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}),
    FactorsThrough f (residualGerbeι X x))

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factorsThrough_iff_range_subset_singleton :
    ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X),
    FactorsThrough f ι ↔ Set.range (Points.map f) ⊆ {x})

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.lift_unique :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] {x : Points X}
    (ι : Z ⟶ X) [IsResidualGerbe ι x] {f : Y ⟶ X} {g g' : Y ⟶ Z}
    (hg : g ≫ ι ≅ f) (hg' : g' ≫ ι ≅ f),
    Nonempty (g ≅ g'))

