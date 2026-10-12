/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Derivation.RegularAdjoinRoot
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.48.4 (07PG)

@stack 07PG
-/


/- Lemma 15.48.4: regularity follows from an absolute derivation taking the defining element to
a unit. -/
@[stacks 07PG "Lemma 15.48.4"]
#check @Derivation.isRegularRing_adjoinRoot_sub_C_of_isUnit
#check @Derivation.isRegularRing_adjoinRoot_sub_C_of_exists
