/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Derivation.RegularQuotient
import StacksCheckRecall

/-!
# Regular principal quotients detected by derivations

Lemma 15.48.2 is the existence form of the canonical derivation criterion for regularity of a
principal quotient.

@stack 07PF
-/

@[expose] public section

/- The primitive API keeps the derivation explicit for later applications. -/
@[stacks 07PF "regular principal quotient from a derivation"]
#check @Derivation.isRegularRing_quotient_principalIdeal_of_isUnit

/- Lemma 15.48.2: if `D f` is a unit modulo `(f)` for some absolute derivation `D`, then
`R ⧸ (f)` is regular. -/
@[stacks 07PF "Lemma 15.48.2"]
#check @Derivation.isRegularRing_quotient_principalIdeal_of_exists
