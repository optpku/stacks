module

public import ReasLib.FieldTheory.PurelyInseparable.Lift
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.42.4

@stack 04KM

Lemma 10.42.4 (Tag 04KM) is a canonical recall of the finite purely
inseparable lift of an essentially finite-type field extension.  The concrete
square and its field-theoretic API are owned by
`FieldExtension.PurelyInseparable.Lift`.
-/

@[stacks 04KM]
#check @FieldExtension.PurelyInseparable.Lift.existsOfEssFiniteType
