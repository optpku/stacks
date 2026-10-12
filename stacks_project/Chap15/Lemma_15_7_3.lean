/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Pullback.BaseChange.Ideal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.7.3

The extended-kernel identity is recalled from the fibre-product base-change ideal API.

@stack 08KN
-/

/- Lemma 15.7.3: extending `ker(B' → B)` to `D'` and then to `C'` agrees with extending
`ker(A' → A)` to `C'`. -/
@[stacks 08KN "Lemma 15.7.3: extended kernel ideal under tensor base change"]
#check @FiberProductBaseChangeSituation.map_map_ker_bprimeToB_eq_map_ker_fromAprime

end
