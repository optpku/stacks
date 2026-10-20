module

public import ReasLib.RingTheory.Jacobson.Ideal
import StacksCheckRecall

/-!
# Jacobson radical criterion

@stack 0AME
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/- Lemma 10.19.1 (1): Stacks `0AME` characterizes the ideals contained in
`Ring.jacobson R` by the units in `1 + I`. -/
@[stacks 0AME "criterion"]
#check (Ideal.le_ringJacobson_iff_isUnit_one_add I :
  I ≤ Ring.jacobson R ↔ ∀ f ∈ I, IsUnit (1 + f))

variable (hI : I ≤ Ring.jacobson R) {x : R}

/- Lemma 10.19.1 (2): under the equivalent conditions above, a unit modulo `I` is already a
unit in `R`. -/
@[stacks 0AME "unit lifting"]
#check (Ideal.isUnit_of_quotient_mk_of_le_ringJacobson I hI :
  IsUnit (Ideal.Quotient.mk I x) → IsUnit x)

#check @Ideal.le_jacobson_bot_iff_isUnit_one_add
#check @Ideal.isUnit_quotient_mk_iff_of_le_jacobson_bot

end Ideal
