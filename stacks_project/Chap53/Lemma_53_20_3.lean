module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 53.20.3 -/
@[stacks 0CD7] #check (AlgebraicGeometry.SmoothOfRelativeDimension.atWorstNodal :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 f] → AlgebraicGeometry.AtWorstNodal f)
