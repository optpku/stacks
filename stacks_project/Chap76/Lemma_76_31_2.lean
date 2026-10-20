module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Target.BaseChange

/-!
# Base change of fibre dimensions of morphisms of algebraic spaces

The target-indexed fibre dimension of a finite type morphism of algebraic
spaces is invariant under arbitrary base change.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 76.31.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a finite type
morphism of algebraic spaces over `S`. The function `fiberDimension f`
associates to a point of `Y` the integer discussed in Lemma 76.31.1.
If `g : Y' ⟶ Y` is a morphism and `f' : X' ⟶ Y'` is the base change of `f`,
then `fiberDimension f' = fiberDimension f ∘ Points.map g`. -/
@[stacks 0D4N] #check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_baseChange :
  ∀ {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.FiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g),
    AlgebraicGeometry.AlgebraicSpace.fiberDimension f' =
      AlgebraicGeometry.AlgebraicSpace.fiberDimension f ∘
        AlgebraicGeometry.AlgebraicSpace.Points.map g)

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_baseChange_apply :
  ∀ {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.FiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g)
    (y' : AlgebraicGeometry.AlgebraicSpace.Points Y'),
    AlgebraicGeometry.AlgebraicSpace.fiberDimension f' y' =
      AlgebraicGeometry.AlgebraicSpace.fiberDimension f
        (AlgebraicGeometry.AlgebraicSpace.Points.map g y'))
