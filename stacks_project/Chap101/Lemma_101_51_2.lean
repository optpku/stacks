/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_9_11_Substack
public import stacks_project.Chap100.Definition_100_11_8_ResidualGerbe
public import stacks_project.Chap100.Example_100_11_9_ResidualGerbe
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_50_1_Decent
public import stacks_project.Chap101.Lemma_101_31_1

/-!
# Factorization through residual gerbes

A morphism of algebraic stacks from a reduced source whose image on points is a
singleton `{x}` factors through a residual gerbe at `x` when the target is
decent or locally Noetherian and its inertia morphism is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Lemma 101.51.2: Let `f : Y ⟶ X` be a morphism of algebraic stacks. Let
`x ∈ |X|` be a point. Assume `X` is decent or locally Noetherian (or both),
`I_X ⟶ X` is quasi-compact, `|f|(|Y|)` is contained in `{x} ⊂ |X|`, and `Y`
is reduced. Then `f` factors through the residual gerbe `Z_x` of `X` at `x`
(whose existence is guaranteed by Lemma 101.31.1 or 101.31.3). -/
@[stacks 0H25]
theorem factorsThrough_of_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι :=
  sorry

/-- If `X` is decent, a morphism from a reduced algebraic stack whose image on
points is contained in `{x}` factors through a residual gerbe at `x`, provided
the inertia morphism of `X` is quasi-compact. -/
theorem factorsThrough_of_isDecent {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsDecent X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι :=
  sorry

/-- If `X` is locally Noetherian, a morphism from a reduced algebraic stack whose
image on points is contained in `{x}` factors through a residual gerbe at `x`,
provided the inertia morphism of `X` is quasi-compact. -/
theorem factorsThrough_of_isLocallyNoetherian {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f ι :=
  sorry

/-- A morphism from a reduced algebraic stack whose image on points is contained
in `{x}` factors through the canonical residual-gerbe inclusion of `X` at `x`. -/
theorem factorsThrough_residualGerbeι {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X}
    [HasResidualGerbe X x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}) :
    FactorsThrough f (residualGerbeι X x) :=
  sorry

/-- A morphism from a reduced algebraic stack factors through a residual gerbe
at `x` if and only if its image on points is contained in `{x}`, provided `X`
is decent or locally Noetherian and `I_X ⟶ X` is quasi-compact. -/
theorem factorsThrough_iff_range_subset_singleton {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] [IsReduced Y]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (hX : IsDecent X ∨ IsLocallyNoetherian X) {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] (f : Y ⟶ X) :
    FactorsThrough f ι ↔ Set.range (Points.map f) ⊆ {x} :=
  sorry

/-- Factorizations through a residual-gerbe monomorphism are unique up to
2-isomorphism. -/
theorem lift_unique {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] {x : Points X}
    (ι : Z ⟶ X) [IsResidualGerbe ι x] {f : Y ⟶ X} {g g' : Y ⟶ Z}
    (hg : g ≫ ι ≅ f) (hg' : g' ≫ ι ≅ f) :
    Nonempty (g ≅ g') :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
