/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Uniqueness
import StacksCheckRecall

/-!
# Residual gerbes from monomorphisms of singleton stacks

A monomorphism from a reduced, locally Noetherian singleton algebraic stack
whose image on points is a single point `x` produces the residual gerbe of
the target at `x`, and is equivalent to it over the target.
-/

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 100.11.12 (1): A monomorphism from a singleton algebraic stack with
point-image `{x}` implies existence of the residual gerbe at `x`. -/
@[stacks 06MX]
#check (AlgebraicGeometry.AlgebraicStack.HasResidualGerbe.of_mono :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {x : Points X} (f : Z ⟶ X) [Groupoids.Hom.Mono f]
    [Nonempty (Points Z)] [Subsingleton (Points Z)],
    Set.range (Points.map f) = {x} → HasResidualGerbe X x)

/- Lemma 100.11.12 (2): The monomorphism from a reduced, locally Noetherian
singleton algebraic stack factors through the canonical residual gerbe by an
equivalence over the ambient stack. -/
@[stacks 06MX]
#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.factors_of_mono :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [IsReduced Z] [IsLocallyNoetherian Z]
    [Nonempty (Points Z)] [Subsingleton (Points Z)] (f : Z ⟶ X)
    [Groupoids.Hom.Mono f] {x : Points X},
    Set.range (Points.map f) = {x} → ∀ [HasResidualGerbe X x],
    ∃ g : Z ⟶ residualGerbe X x,
      (toBasedFunctor g).IsEquivalence ∧
        Nonempty (g ≫ residualGerbeι X x ≅ f))

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.iff :
  ∀ {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X),
    IsResidualGerbe ι x ↔
      Groupoids.Hom.Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧
        Subsingleton (Points Z) ∧ Set.range (Points.map ι) = {x})

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.unique :
  ∀ {S : Scheme.{u}} {X Z Zx : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Zx] {x : Points X}
    (f : Z ⟶ X) (ι : Zx ⟶ X) [IsResidualGerbe f x] [IsResidualGerbe ι x],
    ∃ g : Z ⟶ Zx, (toBasedFunctor g).IsEquivalence ∧ Nonempty (g ≫ ι ≅ f))

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.unique_lift :
  ∀ {S : Scheme.{u}} {X Z Zx : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Zx] {x : Points X}
    (f : Z ⟶ X) (ι : Zx ⟶ X) [IsResidualGerbe f x] [IsResidualGerbe ι x]
    (g g' : Z ⟶ Zx), Nonempty (g ≫ ι ≅ f) → Nonempty (g' ≫ ι ≅ f) →
    Nonempty (g ≅ g'))
