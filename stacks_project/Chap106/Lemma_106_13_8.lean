/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine.Cover
import StacksCheckRecall

/-!
# Étale-local well-nigh affine covers of algebraic stacks with finite inertia

If the inertia morphism of an algebraic stack is finite, the stack admits a
covering by morphisms from well-nigh affine algebraic stacks that are
representable by algebraic spaces, separated, and étale, and that induce an
isomorphism on inertia comparisons.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.13.8: Let `X` be an algebraic stack. Assume the inertia morphism
`forget X : I_X ⟶ X` is finite. Then there exist a set `I` and morphisms of
algebraic stacks `g i : Xi i ⟶ X` such that `|X|` is the union of the images
`|g i|(|Xi i|)`, each `Xi i` is well-nigh affine, each inertia comparison
`I_{Xi i} ⟶ Xi i ×_X I_X` is an isomorphism, and each `g i` is representable
by algebraic spaces, separated, and étale. -/
@[stacks 0DUE] #check
  (AlgebraicGeometry.AlgebraicStack.existsEtaleLocalWellNighAffineCover_of_isFinite_inertia :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [IsFinite (forget.{u + 1, u, u, u + 1} X)],
      ∃ (I : Type (u + 1)) (Xi : I → GroupoidsOver S)
          (hXi : ∀ i, AlgebraicStack (Xi i)) (g : ∀ i, Xi i ⟶ X),
        (⋃ i, Set.range (Points.map (g i))) = Set.univ ∧
          ∀ i, IsWellNighAffine (Xi i) ∧
            (toBasedFunctor (Inertia.comparison (g i))).IsEquivalence ∧
            relativelyRepresentableByAlgebraicSpaces (g i) ∧ Separated (g i) ∧
              Groupoids.Hom.Etale (g i))

#check (AlgebraicGeometry.AlgebraicStack.existsEtaleLocalWellNighAffineChartAt :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] (x : Points X),
    ∃ (Xi : GroupoidsOver S) (hXi : AlgebraicStack Xi) (g : Xi ⟶ X)
      (xi : Points Xi),
      Points.map g xi = x ∧ IsWellNighAffine Xi ∧
        (toBasedFunctor (Inertia.comparison g)).IsEquivalence ∧
        relativelyRepresentableByAlgebraicSpaces g ∧ Separated g ∧
          Groupoids.Hom.Etale g)

end AlgebraicGeometry.AlgebraicStack
