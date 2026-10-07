module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.ConnectedComponent
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry

/- Definition 29.26.3: a connected component of a scheme carries a unique scheme structure for
which its canonical closed immersion into the scheme is flat. -/
@[stacks 04PX] #check
  (AlgebraicGeometry.Scheme.existsUnique_flatIdealSheafData_connectedComponent :
    ∀ (X : Scheme.{u}) (C : ConnectedComponents X),
      ∃! I : X.IdealSheafData,
        Flat I.subschemeι ∧ (I.support : Set X) = C.set)
