module

public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
import StacksCheckRecall

/-!
# Lemma 10.45.4
@stack 046W
-/

@[expose] public section

/-!
# Uniqueness of Perfect Closures

Lemma 10.45.4 is a canonical recall of the unique algebra equivalence from
the relative perfect closure in an algebraic closure to any perfect purely
inseparable field extension.
-/

/- The canonical subextension `perfectClosure k (AlgebraicClosure k)` is purely inseparable over
`k` and is a perfect field. -/
@[stacks 046W "canonical perfect closure"]
#check @perfectClosure.isPurelyInseparable
@[stacks 046W "canonical perfect closure"]
#check @perfectClosure.perfectField

/- Lemma 10.45.4 (Tag 046W): any perfect purely inseparable extension of `k` is uniquely
`k`-isomorphic to `perfectClosure k (AlgebraicClosure k)`. -/
@[stacks 046W]
#check @FieldExtension.PerfectClosure.existsUnique_algEquiv
