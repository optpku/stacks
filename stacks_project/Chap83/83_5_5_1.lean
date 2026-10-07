module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pairings
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PreRelation

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)

/- 83.5.5.1 (1): the diagonal `j_diag : U ⟶ U ⨯ U` sending `u` to `(u, u)`. -/
@[stacks 048S] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.diagonalPairing U : U ⟶ U ⨯ U)

/- 83.5.5.1 (2): the flip `j_flip : R ⟶ U ⨯ U` sending `r` to `(s(r), t(r))`. -/
@[stacks 048S] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.flipHom P : P.left ⟶ U ⨯ U)

/- 83.5.5.1 (3): the transitivity pairing `j_comp : pullback P.s P.t ⟶ U ⨯ U`
sending `(r, r')` to `(t(r), s(r'))`. -/
@[stacks 048S] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.compPair P : pullback P.s P.t ⟶ U ⨯ U)
