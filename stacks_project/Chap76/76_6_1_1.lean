module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Piece

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 09RP::statement_repair::1
The canonical pushforward comparison identifies every conormal degree piece
with the successive quotient of the coborder ideal. -/
@[stacks 09RP] #check
  (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piece_pushforward :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
      IsIso (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piecePushforwardComparison i n))
