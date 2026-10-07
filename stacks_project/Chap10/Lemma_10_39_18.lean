module

public import ReasLib.RingTheory.Flat.Localization.AtPrime
public import ReasLib.RingTheory.Localization.TensorProduct
import StacksCheckRecall

/-!
# Lemma 10.39.18

@stack 00HT
-/

@[expose] public section

/- Lemma 10.39.18, tag `00HT`, is a canonical recall block.  Its five local criteria are owned
by `Module.Flat.iff_forall_atPrime`, `Module.Flat.iff_forall_atMaximal`,
`Module.Flat.iff_forall_away_of_span_range_eq_top`,
`Module.Flat.iff_forall_atPrimeOver`, and `Module.Flat.iff_forall_atMaximalOver`.
The reusable tensor-localization comparison is `LocalizedModule.tensorRightLinearEquiv`. -/
@[stacks 00HT "prime-local flatness criterion"]
#check @Module.Flat.iff_forall_atPrime
@[stacks 00HT "maximal-local flatness criterion"]
#check @Module.Flat.iff_forall_atMaximal
@[stacks 00HT "away-local flatness criterion"]
#check @Module.Flat.iff_forall_away_of_span_eq_top
@[stacks 00HT "finite away-local flatness criterion"]
#check @Module.Flat.iff_forall_away_of_span_range_eq_top
@[stacks 00HT "relative prime-local flatness criterion"]
#check @Module.Flat.iff_forall_atPrimeOver
@[stacks 00HT "relative maximal-local flatness criterion"]
#check @Module.Flat.iff_forall_atMaximalOver
@[stacks 00HT "flatness through a localization tower"]
#check @Module.Flat.localizedModule_of_tower
@[stacks 00HT "flatness at a prime over the base"]
#check @Module.Flat.atPrimeOver
@[stacks 00HT "tensor localization comparison"]
#check @LocalizedModule.tensorRightLinearEquiv
