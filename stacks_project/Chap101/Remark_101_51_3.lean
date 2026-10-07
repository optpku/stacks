module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap100.Lemma_100_4_7_Topology
public import stacks_project.Chap101.Lemma_101_51_2

/-!
# Factorization through residual gerbes at closed points

If `X` is a locally Noetherian algebraic stack and `x` is a closed point of
`|X|`, a morphism from a reduced algebraic stack whose image on points is
contained in `{x}` factors through a residual gerbe at `x`, even without
quasi-compactness of the inertia morphism `I_X ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Remark 101.51.3: it is unknown whether Lemma 101.51.2 remains true if one
assumes only that `X` is locally Noetherian, dropping quasi-compactness of
`I_X ⟶ X`. If in addition `x` is a closed point of `|X|`, then a morphism
`f : Y ⟶ X` of algebraic stacks from a reduced source with
`Set.range (Points.map f) ⊆ {x}` still factors through a residual gerbe of
`X` at `x` (whose existence is guaranteed by Lemma 101.31.3). -/
@[stacks 0H26]
theorem factorsThrough_of_mem_closedPoints {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι :=
  sorry

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through the canonical residual-gerbe inclusion of `X` at a
closed point `x`, when `X` is locally Noetherian. -/
theorem factorsThrough_residualGerbeι_of_mem_closedPoints {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [IsReduced Y] [IsLocallyNoetherian X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) [HasResidualGerbe X x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f (residualGerbeι X x) :=
  sorry

/-- A morphism from a reduced algebraic stack factors through a residual gerbe
at a closed point `x` if and only if its image on points is contained in `{x}`,
when `X` is locally Noetherian. -/
theorem factorsThrough_iff_range_subset_singleton_of_mem_closedPoints
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] [AlgebraicStack Z] [IsReduced Y]
    [IsLocallyNoetherian X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) (ι : Z ⟶ X) [IsResidualGerbe ι x]
    (f : Y ⟶ X) :
    FactorsThrough f ι ↔ Set.range (Points.map f) ⊆ {x} :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
