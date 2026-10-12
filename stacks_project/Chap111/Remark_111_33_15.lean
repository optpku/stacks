/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
variable [IsAffine X] [IsAffine Y] [S.IsSeparated]

/- Remark 111.33.15: a fibre product of affine schemes over a separated scheme is affine. -/
@[stacks 02EZ]
#check (AlgebraicGeometry.Scheme.Pullback.isAffine_of_isSeparated f g :
  IsAffine (pullback f g))
