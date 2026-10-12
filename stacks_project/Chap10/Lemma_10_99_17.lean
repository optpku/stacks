/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.Away
import StacksCheckRecall

/-!
# Flatness from a finite away cover

@stack 0H7P

The shared owner keeps the finite generating family visible because its cardinality controls the
required range of positive `Tor` vanishing. It also handles the empty family, and therefore
strictly generalizes the source assumption `1 ≤ r`.
-/

@[expose] public section

/- Lemma 10.99.17 (Tag 0H7P) (1): the finite away-localization, quotient-flatness, and positive
`Tor` hypotheses imply flatness. -/
@[stacks 0H7P "(1)"]
#check @Module.Flat.of_away_of_quotient_of_isZero_tor

/- Lemma 10.99.17 (Tag 0H7P) (2): the same criterion holds with flatness replaced throughout
by faithful flatness. -/
@[stacks 0H7P "(2)"]
#check @Module.FaithfullyFlat.of_away_of_quotient_of_isZero_tor
