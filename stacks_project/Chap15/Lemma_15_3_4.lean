/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Projective.Jacobson
import StacksCheckRecall

/-!
# Lemma 15.3.4

@stack 0D48
-/

@[expose] public section

/- Lemma 15.3.4: a finite flat module whose reduction modulo an ideal in the Jacobson radical
is projective is itself finite projective. -/
@[stacks 0D48 "Lemma 15.3.4"]
#check @Module.Projective.of_quotient_of_le_jacobson
