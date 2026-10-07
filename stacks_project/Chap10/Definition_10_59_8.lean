module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Degree
import StacksCheckRecall

/-!
# Definition 10.59.8

@stack 00KA
-/

@[expose] public section

/- Definition 10.59.8 (Stacks 00KA): the Hilbert--Samuel degree of a finite module over a
Noetherian local ring is owned by the reusable `Ideal.HilbertSamuel` API. -/
@[stacks 00KA]
#check @Ideal.HilbertSamuel.degree

@[stacks 00KA "Hilbert-Samuel chi polynomial"]
#check @Ideal.HilbertSamuel.chiPolynomial
@[stacks 00KA "chi polynomial specification"]
#check @Ideal.HilbertSamuel.chiPolynomial_spec
@[stacks 00KA "ideal-of-definition invariance"]
#check @Ideal.HilbertSamuel.degree_eq_of_isIdealOfDefinition
@[stacks 00KA "eventual-equality invariance"]
#check @Ideal.HilbertSamuel.degree_eq_of_eventuallyEq
@[stacks 00KA "linear-equivalence invariance"]
#check @Ideal.HilbertSamuel.degree_eq_of_linearEquiv
@[stacks 00KA "zero-ideal specialization"]
#check @Ideal.HilbertSamuel.degree_eq_bot
