module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek

@[expose] public section

open AlgebraicGeometry

universe u

/- The chapter-facing compatibility surface uses the reusable Noetherian instance. -/
#check
  (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.instIsNoetherian :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [IsNoetherian S]
      (X : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S),
      IsNoetherian X.obj.left)
