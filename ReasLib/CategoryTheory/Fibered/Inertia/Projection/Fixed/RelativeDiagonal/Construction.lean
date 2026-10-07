module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.RelativeDiagonal.Construction
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred relative diagonal construction

This leaf owns the relative diagonal in the fixed fibred-category owner.
Projection readouts live in `RelativeDiagonal.Computations`.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedOwner

variable {X Y :
  FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The neutral relative diagonal preserves strongly cartesian morphisms in the fixed
fibred-category owner. -/
theorem relativeDiagonal.preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedFunctor.relativeDiagonal
      (toBasedFunctor F)).PreservesStronglyCartesian := sorry
/- Proof strategy: both projections of the relative diagonal are the identity on the source.
Use detection of cartesian morphisms by the two pseudo-pullback projections. -/

/-- The relative diagonal retained as a morphism in the fixed bicategory of fibred categories. -/
@[stacks 034H "fibred relative diagonal"]
def relativeDiagonal (F : X ⟶ Y) :
    X ⟶ LocallyInduced.TwoFibreProduct.apex F F :=
  ofBasedFunctor
    (BasedFunctor.relativeDiagonal (toBasedFunctor F))
    (RelativeInertia.relativeDiagonal.preservesStronglyCartesian F)

/-- Forgetting the fibred-category owner from the relative diagonal recovers the neutral based
relative diagonal. -/
@[simp]
theorem relativeDiagonal.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (RelativeInertia.relativeDiagonal F) =
      BasedFunctor.relativeDiagonal (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The total functor underlying the fibred relative diagonal is the neutral based relative
diagonal functor. -/
@[simp]
theorem relativeDiagonal.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F) =
      (BasedFunctor.relativeDiagonal (FiberedCategoryOver.toBasedFunctor F)).toFunctor := sorry

end FixedOwner

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
