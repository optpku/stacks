module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange.Bijective
import StacksCheckRecall

/-!
# Lemma 15.90.2 (05E9)

The tensor-unit criterion is recalled from the canonical ideal-power torsion
base-change API.

@stack 05E9
-/

@[expose] public section

/- Lemma 15.90.2 (05E9): under flat faithful base change, the tensor unit is
bijective on every ideal-power torsion module exactly when the quotient map
modulo `I` is bijective. -/
@[stacks 05E9]
#check @ModuleCat.IdealPower.BaseChange.tensorUnit_bijective_iff_quotientByIdeal_bijective

#check @ModuleCat.IdealPower.BaseChange.restricted
#check @RingHom.Flat.quotientByIdeal_pow_bijective
