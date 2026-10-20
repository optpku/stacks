module

public import ReasLib.AlgebraicGeometry.Hilbert.AddPoint
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/- Lemma 44.3.4: for a smooth separated relative curve with representable Hilbert functors, the
morphism `(D, x) ↦ D + x` from the degree-`d` Hilbert scheme times `X` to the degree-`d + 1`
Hilbert scheme is finite locally free of rank `d + 1`. -/
@[stacks 0B9G] #check
  (AlgebraicGeometry.Hilbert.addPointMap_isFiniteLocallyFreeOfRank :
    ∀ {S : Scheme.{u}} (X : Over S)
      [SmoothOfRelativeDimension 1 X.hom] [IsSeparated X.hom]
      [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ),
      IsFiniteLocallyFreeOfRank (addPointMap X d).left (d + 1))

end AlgebraicGeometry.Hilbert
