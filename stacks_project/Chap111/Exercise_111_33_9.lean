module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.InfiniteAffineCounterexample
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.PuncturedAffineSpace
open AlgebraicGeometry.InfiniteAffineCounterexample

universe u

namespace AlgebraicGeometry.InfiniteAffineCounterexample

/- Exercise 111.33.9: the glued closed subscheme of the punctured spectrum does not extend
to a closed subscheme of the ambient infinite affine scheme. -/
@[stacks 028V] #check (AlgebraicGeometry.InfiniteAffineCounterexample.closedSubscheme_not_extends :
  (k : Type u) → [Field k] →
    ¬ ∃ (J : (AlgebraicGeometry.PuncturedAffineSpace.coordinateSpectrum ℕ k).IdealSheafData),
      J.comap (AlgebraicGeometry.PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).ι =
        AlgebraicGeometry.InfiniteAffineCounterexample.idealSheaf k)

end AlgebraicGeometry.InfiniteAffineCounterexample
