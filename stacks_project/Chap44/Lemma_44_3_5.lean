module

public import ReasLib.AlgebraicGeometry.Hilbert.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/- Lemma 44.3.5: if `X ⟶ S` is a smooth relative curve and all its Hilbert functors are
representable, then the degree-`d` representing scheme is smooth over `S` of relative
dimension `d`. -/
@[stacks 0B9H] #check
  (AlgebraicGeometry.Hilbert.representingScheme_smoothOfRelativeDimension :
    ∀ {S : Scheme.{u}} (X : Over S)
      [SmoothOfRelativeDimension 1 X.hom]
      [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ),
      SmoothOfRelativeDimension d (functor X d).reprX.hom)

end AlgebraicGeometry.Hilbert
