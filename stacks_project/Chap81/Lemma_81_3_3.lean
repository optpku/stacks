module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CartesianSystem
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Colimit.Etale
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 81.3.3
A cocone of algebraic spaces over a base is colimiting if spaces-étale pullback is
an equivalence and affine étale cocones of maps extend uniquely. -/
@[stacks 0GHL] #check
  (AlgebraicGeometry.AlgebraicSpace.isColimit_of_spacesEtalePullback :
    ∀ {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
      (D : J ⥤ Over B) (c : Cocone D),
      IsSpacesEtalePullbackEquivalence c → HasAffineEtaleCoconeExtension c →
        Nonempty (IsColimit c))
