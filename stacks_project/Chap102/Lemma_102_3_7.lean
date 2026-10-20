module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LimitPreserving.FinitePresentation

/-!
# Algebraic stacks locally of finite presentation are limit preserving

An algebraic stack over a scheme `S` whose structure morphism is locally of
finite presentation is limit preserving in the sense of Artin's Axioms
Definition 98.11.1. Equivalently, the structure morphism itself is limit
preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 102.3.7: Let `S` be a scheme. Let `𝒳` be an algebraic stack over `S`.
If `𝒳 ⟶ S` is locally of finite presentation, then `𝒳` is limit preserving
in the sense of Artin's Axioms, Definition 98.11.1 (equivalently: the morphism
`𝒳 ⟶ S` is limit preserving). -/
@[stacks 0CMX] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.toLimitPreserving :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X]
      [AlgebraicStack.LocallyOfFinitePresentation (baseProjection.{u + 1, u, u + 1} X)],
      Groupoids.LimitPreserving X)

/- The structure morphism of an algebraic stack locally of finite presentation
over `S` is limit preserving as a 1-morphism of categories fibred in groupoids. -/
#check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.toHomLimitPreserving :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X]
      [AlgebraicStack.LocallyOfFinitePresentation (baseProjection.{u + 1, u, u + 1} X)],
      Groupoids.Hom.LimitPreserving (baseProjection.{u + 1, u, u + 1} X))

/- A category fibred in groupoids over `(Sch/S)_fppf` is limit preserving if and
only if its structure morphism to `(Sch/S)_fppf` is limit preserving. -/
#check
  (AlgebraicGeometry.Groupoids.LimitPreserving.iff_baseProjection :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
      Groupoids.LimitPreserving X ↔
        Groupoids.Hom.LimitPreserving (baseProjection.{u + 1, u, u + 1} X))
