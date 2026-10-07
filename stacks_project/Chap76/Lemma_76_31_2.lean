module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap76.Lemma_76_31_1_FiberDimension

/-!
# Base change of fibre dimensions of morphisms of algebraic spaces

The target-indexed fibre dimension of a finite type morphism of algebraic
spaces is invariant under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.31.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a finite type
morphism of algebraic spaces over `S`. The function `fiberDimension f`
associates to a point of `Y` the integer discussed in Lemma 76.31.1.
If `g : Y' ⟶ Y` is a morphism and `f' : X' ⟶ Y'` is the base change of `f`,
then `fiberDimension f' = fiberDimension f ∘ Points.map g`. -/
@[stacks 0D4N]
theorem fiberDimension_baseChange {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    fiberDimension f' = fiberDimension f ∘ Points.map g :=
  sorry

/-- Evaluating the base-change identity for fibre dimensions at a point of
the new target. -/
theorem fiberDimension_baseChange_apply {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (y' : Points Y') :
    fiberDimension f' y' = fiberDimension f (Points.map g y') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
