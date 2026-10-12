/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Filtration.ArtinRees.Ideal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.51.2 (Artin-Rees)

@stack 00IN
-/

@[stacks 00IN "Artin-Rees owner"]
#check @Ideal.exists_pow_inf_eq_pow_smul

@[stacks 00IN "cutoff above a prescribed bound"]
#check @Ideal.exists_ge_pow_inf_eq_pow_smul

@[stacks 00IN "positive Artin-Rees cutoff"]
#check @Ideal.exists_pos_pow_inf_eq_pow_smul
