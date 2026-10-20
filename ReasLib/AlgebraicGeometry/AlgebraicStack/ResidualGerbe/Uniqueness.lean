/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe

/-!
# Uniqueness and factorization of residual gerbes

Residual gerbes at the same point are equivalent over the ambient algebraic
stack. Monomorphisms from reduced locally Noetherian singleton stacks factor
through the canonical residual gerbe by an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- Any two residual gerbes of an algebraic stack at the same point are
equivalent over that stack. -/
theorem unique {S : Scheme.{u}} {X Z Zx : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Zx] {x : Points X}
    (f : Z ⟶ X) (ι : Zx ⟶ X) [IsResidualGerbe f x] [IsResidualGerbe ι x] :
    ∃ g : Z ⟶ Zx, (toBasedFunctor g).IsEquivalence ∧ Nonempty (g ≫ ι ≅ f) :=
  sorry

/-- Comparison 1-morphisms between residual gerbes at the same point are unique
up to 2-isomorphism. -/
theorem unique_lift {S : Scheme.{u}} {X Z Zx : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Zx] {x : Points X}
    (f : Z ⟶ X) (ι : Zx ⟶ X) [IsResidualGerbe f x] [IsResidualGerbe ι x]
    (g g' : Z ⟶ Zx) (hg : Nonempty (g ≫ ι ≅ f))
    (hg' : Nonempty (g' ≫ ι ≅ f)) :
    Nonempty (g ≅ g') :=
  sorry

/-- A monomorphism from a reduced, locally Noetherian singleton algebraic stack
with point-image `{x}` factors through the canonical residual gerbe at `x` by an
equivalence, with the factorization commuting up to 2-isomorphism. -/
theorem factors_of_mono {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [IsReduced Z] [IsLocallyNoetherian Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)] (f : Z ⟶ X)
    [Groupoids.Hom.Mono f] {x : Points X}
    (hx : Set.range (Points.map f) = {x}) [HasResidualGerbe X x] :
    ∃ g : Z ⟶ residualGerbe X x,
      (toBasedFunctor g).IsEquivalence ∧
        Nonempty (g ≫ residualGerbeι X x ≅ f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
