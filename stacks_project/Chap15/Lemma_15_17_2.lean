/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.FlatQuotient.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.17.2

@stack 0525

For an Artinian ring, the least ideal with flat quotient is detected after arbitrary base change:
the tensor product is flat exactly when the image of that ideal is zero.  The theorem is owned by
`Ideal.flat_baseChange_iff_map_eq_bot`; the factorization and tensor maps used in its proof are
shared under `Ideal.FlatQuotient`.
-/

/- Lemma 15.17.2 (Stacks `0525`): flatness after base change is equivalent to vanishing of the
image of the least flat-quotient ideal. -/
@[stacks 0525 "flat base change detects the least flat-quotient ideal"]
#check @Ideal.flat_baseChange_iff_map_eq_bot

@[stacks 0525 "quotient factorization data"]
#check @Ideal.FlatQuotient.factorAlgHom
#check @Ideal.FlatQuotient.kernelAlgHom
#check @Ideal.FlatQuotient.factorTensor
#check @Ideal.FlatQuotient.baseTensor

end
