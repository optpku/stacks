module

import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 87.37.2: For a formal algebraic space over a scheme and a closed subset
of its reduction, the subfunctor of sections whose image lies in that subset
is a formal algebraic space. -/
@[stacks 0GVR] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isFormalAlgebraicSpace :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
      [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
      (R : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X)
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points R.space)),
      AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace
        (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.functor R T))
