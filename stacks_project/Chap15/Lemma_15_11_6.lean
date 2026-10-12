/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.PairCriteria
import StacksCheckRecall

/-!
# Equivalent criteria for henselian pairs

Lemma 15.11.6 is owned by `Ideal.HenselianPairCriteria`. The predicates and named binary views
are recalled directly so the chapter does not introduce parallel root-level spellings.

@stack 09XI
-/

@[expose] public section

@[stacks 09XI "five equivalent criteria for a henselian pair"]
#check @Ideal.HenselianPairCriteria.tfae

@[stacks 09XI "henselianity and etale-section lifting"]
#check @Ideal.HenselianPairCriteria.henselian_iff_etaleLift

@[stacks 09XI "henselianity and finite-algebra idempotent lifting"]
#check @Ideal.HenselianPairCriteria.henselian_iff_finiteIdempotentLifting

@[stacks 09XI "henselianity and integral-algebra idempotent lifting"]
#check @Ideal.HenselianPairCriteria.henselian_iff_integralIdempotentLifting

@[stacks 09XI "henselianity and the Gabber root criterion"]
#check @Ideal.HenselianPairCriteria.henselian_iff_gabber

@[stacks 09XI "Gabber criterion implies henselianity"]
#check @Ideal.SatisfiesGabberRootCriterion.henselianRing

@[stacks 09XI "idempotents modulo a henselian ideal"]
#check @Ideal.HenselianPairCriteria.idempotentMap_bijective

@[stacks 09XI "uniqueness in the Gabber root criterion"]
#check @Ideal.SatisfiesGabberRootCriterion.existsUnique
