/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Derivation
import StacksCheckRecall

@[expose] public section

/-!
# Normalization in a Degree-p Purely Inseparable Extension

@stack 0AE0
-/

/- Lemma 10.161.10: a derivation which does not kill the defining element forces the
normalization in the associated degree-`p` extension to be finite. -/
@[stacks 0AE0]
#check @IsIntegrallyClosed.integralClosure_adjoinRoot_pthSub_finite_of_derivation

/- The nonvanishing derivative also gives the canonical irreducibility input for the extension. -/
@[stacks 0AE0 "irreducible p-th-root polynomial companion"]
#check @X_pow_sub_C_irreducible_of_prime
