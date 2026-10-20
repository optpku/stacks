module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedPoints
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.33.5: a nonempty quasi-compact scheme has a closed point. -/
@[stacks 028S] #check (AlgebraicGeometry.Scheme.exists_closedPoint_of_compactSpace :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] [Nonempty X],
    (closedPoints X).Nonempty)
