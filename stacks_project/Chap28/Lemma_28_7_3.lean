module

public import ReasLib.AlgebraicGeometry.Scheme.Normal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 28.7.3: a normal scheme is reduced. -/
@[stacks 033K] #check (AlgebraicGeometry.Scheme.isReduced_of_isNormal :
  ∀ {X : Scheme.{u}}, X.isNormal → AlgebraicGeometry.IsReduced X)
