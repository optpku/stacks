module

public import ReasLib.LinearAlgebra.Matrix.Adjugate.RowPartition
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.15.6

@stack 080R

The row-partition and adjugate identities are recalled directly from their matrix owner, which is
generic in the row index types and therefore subsumes the source's `Fin` specialization.
-/

/- The lower block entries are determinants of the corresponding row-replacement matrices. -/
@[stacks 080R "row-replacement determinant formula"]
#check @Matrix.toRows₂_mul_adjugate_apply

/- Lemma 10.15.6: multiplying by the adjugate of the top square block gives the displayed block
matrix. -/
@[stacks 080R "row-partition adjugate formula"]
#check @Matrix.mul_toRows₁_adjugate

#check @Matrix.vecMul_adjugate_apply
#check @Matrix.fromRows_mul_adjugate

end
