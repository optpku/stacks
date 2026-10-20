module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.InfiniteSquareRootCounterexample
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Example 29.38.4

The reusable owner constructs the infinite square-root quotient, its weighted projective
spectrum and canonical twists, and the affine-chart obstruction to relative very ampleness.
-/

/- Example 29.38.4: no natural tensor power of the degree-one twist on the infinite square-root
projective spectrum is relatively very ample over the base field. -/
@[stacks 01VO] #check
  (AlgebraicGeometry.Proj.InfiniteSquareRootCounterexample.no_tensorPower_relativelyVeryAmple :
    ∀ (k : Type u) [Field k] (n : ℕ),
      ¬ AlgebraicGeometry.RelativelyVeryAmple
        (AlgebraicGeometry.Proj.InfiniteSquareRootCounterexample.toSpec k)
        (AlgebraicGeometry.RingedSpace.TensorPower.sheaf
          (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf
            (AlgebraicGeometry.Proj.InfiniteSquareRootCounterexample.grading k) 1) n))
