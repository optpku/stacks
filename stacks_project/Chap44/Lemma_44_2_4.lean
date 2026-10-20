module

public import ReasLib.AlgebraicGeometry.Hilbert.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/- Lemma 44.2.4: if `X ⟶ S` is separated and the degree-`d` Hilbert functor is
representable, then its chosen representing scheme is separated over `S`. -/
@[stacks 0B98] #check
  (AlgebraicGeometry.Hilbert.representingScheme_isSeparated :
    ∀ {S : Scheme.{u}} (X : Over S) (d : ℕ)
      [IsSeparated X.hom] [(functor X d).IsRepresentable],
      IsSeparated (functor X d).reprX.hom)

end AlgebraicGeometry.Hilbert
