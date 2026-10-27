/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.Factorization

/-!
# Factorization through residual gerbes

A morphism of algebraic stacks from a reduced source whose image on points is contained in the
singleton `{x}` factors through a residual gerbe at `x` when the target is
decent or locally Noetherian and its inertia morphism is quasi-compact.
For a locally Noetherian target and a closed point `x`, the factorization holds
without quasi-compactness of inertia.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through any residual-gerbe inclusion at `x`, provided the target
is decent or locally Noetherian and its canonical inertia projection is
quasi-compact. -/
@[stacks 0H25]
theorem factorsThrough_of_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι := sorry

/-- If `X` is decent, a morphism from a reduced algebraic stack whose image on
points is contained in `{x}` factors through a residual gerbe at `x`, provided
the inertia morphism of `X` is quasi-compact. -/
theorem factorsThrough_of_isDecent {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsDecent X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι := sorry

/-- If `X` is locally Noetherian, a morphism from a reduced algebraic stack whose
image on points is contained in `{x}` factors through a residual gerbe at `x`,
provided the inertia morphism of `X` is quasi-compact. -/
theorem factorsThrough_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι := sorry

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through the canonical residual-gerbe inclusion of `X` at `x`,
provided `X` is decent or locally Noetherian and its canonical inertia projection
is quasi-compact. -/
theorem factorsThrough_residualGerbeι {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X}
    (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f (residualGerbeι X x) := sorry

/-- A morphism from a reduced algebraic stack factors through a residual gerbe
at `x` if and only if its image on points is contained in `{x}`, provided `X`
is decent or locally Noetherian and `I_X ⟶ X` is quasi-compact. -/
theorem factorsThrough_iff_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X) :
    FactorsThrough f ι ↔ Set.range (Points.map f) ⊆ {x} := sorry

/-- Factorizations through a residual-gerbe monomorphism are unique up to
2-isomorphism. -/
theorem lift_unique {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] {x : Points X}
    (ι : Z ⟶ X) [IsResidualGerbe ι x] {f : Y ⟶ X} {g g' : Y ⟶ Z}
    (hg : g ≫ ι ≅ f) (hg' : g' ≫ ι ≅ f) :
    Nonempty (g ≅ g') := sorry

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through any residual-gerbe inclusion at a closed point `x` of a
locally Noetherian algebraic stack, without a quasi-compactness assumption on
inertia. -/
@[stacks 0H26]
theorem factorsThrough_of_mem_closedPoints {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι := sorry

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through the canonical residual-gerbe inclusion of `X` at a
closed point `x`, when `X` is locally Noetherian. -/
theorem factorsThrough_residualGerbeι_of_mem_closedPoints {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [IsReduced Y] [IsLocallyNoetherian X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f (residualGerbeι X x) := sorry

/-- A morphism from a reduced algebraic stack factors through a residual gerbe
at a closed point `x` if and only if its image on points is contained in `{x}`,
when `X` is locally Noetherian. -/
theorem factorsThrough_iff_range_subset_singleton_of_mem_closedPoints
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] [AlgebraicStack Z] [IsReduced Y]
    [IsLocallyNoetherian X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) (ι : Z ⟶ X) [IsResidualGerbe ι x]
    (f : Y ⟶ X) :
    FactorsThrough f ι ↔ Set.range (Points.map f) ⊆ {x} := sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
