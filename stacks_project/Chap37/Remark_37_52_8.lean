module

public import stacks_project.Chap37.Lemma_37_52_4
public import stacks_project.Chap37.Lemma_37_52_7
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Remark 37.52.8: when `S` is locally Noetherian, Lemma 37.52.7 gives an
alternative proof of Lemma 37.52.4 by localizing at `f x'`, inducting on the
dimension, and using the resulting quasi-finite closed subscheme to descend to
a strictly smaller-dimensional local ring. -/
@[stacks 05GV] #check
  (AlgebraicGeometry.Scheme.Hom.closure_closedPoints_between_specializations :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X),
      Specializes x x' →
      f.asFiber x' ∈ closedPoints (f.fiber (f x')) →
      closure
          {x₁ : f.fiber (f x) |
            x₁ ∈ closedPoints (f.fiber (f x)) ∧
              Specializes (f.asFiber x) x₁ ∧
              Specializes (f.fiberι (f x) x₁) x'} =
        closure ({f.asFiber x} : Set (f.fiber (f x))))

end AlgebraicGeometry.Scheme.Hom

end
