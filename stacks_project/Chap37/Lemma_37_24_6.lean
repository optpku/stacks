module

public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Fiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.24.6: reduction of the fibre at a generic point is canonically isomorphic to the
fibre at that point of the reduced scheme. -/
@[stacks 054Z] #check
  (AlgebraicGeometry.Scheme.Hom.reductionFiberComparison_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (η : genericPoints Y),
      IsIso (AlgebraicGeometry.Scheme.Hom.reductionFiberComparison f η))
