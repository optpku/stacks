module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.LimitPreserving
import StacksCheckRecall

/-!
# Morphisms of algebraic stacks locally of finite presentation

A morphism of algebraic stacks is limit preserving if and only if it is
limit preserving on objects, if and only if it is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Proposition 102.3.8: Let `f : 𝒳 ⟶ 𝒴` be a morphism of algebraic stacks.
The following are equivalent: `f` is limit preserving, `f` is limit
preserving on objects, and `f` is locally of finite presentation. -/
@[stacks 0CMY] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.tfae :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      List.TFAE [Groupoids.Hom.LimitPreserving f,
        Groupoids.Hom.LimitPreservingOnObjects f,
        AlgebraicStack.LocallyOfFinitePresentation f])

#check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.iff_limitPreservingOnObjects :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Groupoids.Hom.LimitPreserving f ↔ Groupoids.Hom.LimitPreservingOnObjects f)

#check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.iff_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Groupoids.Hom.LimitPreserving f ↔ AlgebraicStack.LocallyOfFinitePresentation f)

#check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.of_limitPreservingOnObjects :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [Groupoids.Hom.LimitPreservingOnObjects f],
      AlgebraicStack.LocallyOfFinitePresentation f)

#check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.homLimitPreserving :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [AlgebraicStack.LocallyOfFinitePresentation f],
      Groupoids.Hom.LimitPreserving f)
