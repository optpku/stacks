module

public import ReasLib.AlgebraicGeometry.Hilbert.Representability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 44.2.5: for a morphism `X ⟶ S` of affine schemes and `d : ℕ`, the
degree-`d` Hilbert functor `Hilbert.functor X d` is representable. -/
@[stacks 0B99] #check
  (AlgebraicGeometry.Hilbert.functor_isRepresentable_of_isAffine :
    ∀ {S : Scheme.{u}} (X : Over S) (d : ℕ)
      [IsAffine X.left] [IsAffine S],
      (AlgebraicGeometry.Hilbert.functor X d).IsRepresentable)
