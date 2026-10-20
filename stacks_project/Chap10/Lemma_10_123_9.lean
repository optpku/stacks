module

public import Mathlib.RingTheory.ZariskisMainTheorem
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.9 (Tag 00Q1): strong transcendence obstructs quasi-finiteness.

@stack 00Q1
-/

/- Lemma 10.123.9: finite generation over a strongly transcendental element
contradicts quasi-finiteness.  The weakly-quasi-finite theorem is the core
owner; the second check is its quasi-finite specialization. -/
@[stacks 00Q1 "weakly quasi-finite obstruction owner"]
#check @Algebra.not_isStronglyTranscendental_of_weaklyQuasiFiniteAt

@[stacks 00Q1 "quasi-finite specialization"]
#check @Algebra.not_isStronglyTranscendental_of_quasiFiniteAt
