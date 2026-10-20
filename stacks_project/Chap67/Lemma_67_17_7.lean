module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.Immersion
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.17.7: Let S be a scheme and f : X ⟶ Y an immersion of algebraic
spaces over S. Assume either f is quasi-compact or X is reduced. Let Z be the
scheme-theoretic image of f, with factorization toImage : X ⟶ Z and ι : Z ⟶ Y.
Then toImage is an open immersion identifying X with a scheme-theoretically
dense open subspace of Z. Moreover, X is topologically dense in Z. -/
@[stacks 088G] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.isOpenImmersion_and_dense_toImage_of_quasiCompact_or_isReduced :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [IsImmersion f] [IsSchemeTheoreticImage f toImage ι],
      (QuasiCompact f ∨ IsReduced X) →
        IsOpenImmersion toImage ∧ Open.IsSchemeTheoreticallyDense toImage ∧ Dominant toImage)

end AlgebraicGeometry.AlgebraicSpace
