module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Definition 73.4.9: in the situation of Lemma 73.4.8, the identity-base inverse
image `inverseImage (𝟙 X)` (that is, `i_X⁻¹ = π_{X,*}`) is called restriction to
the small étale site, from sheaves on the big étale site `(Spaces/X)_étale` to
sheaves on `X_spaces,étale`; its value on a big-étale sheaf `F` is denoted
`F|_{X_étale}`. -/
@[stacks 0DF4] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.inverseImage (𝟙 X) :
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology X) (Type (u + 1)))
