module

public import ReasLib.RingTheory.CohenMacaulay.Polynomial
import StacksCheckRecall

/-!
# Lemma 10.104.7

@stack 00ND
-/

@[expose] public section

/-
Lemma 10.104.7 (Stacks tag `00ND`) is a chapter-facing recall of the
ring-level polynomial closure theorem.  The arbitrary finite-variable owner
is `CohenMacaulayRing.mvPolynomial`; this source view fixes `Fin n`.
-/

@[stacks 00ND]
#check @CohenMacaulayRing.mvPolynomial_fin
