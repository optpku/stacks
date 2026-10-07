module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.1 (Tag 00PQ): a polynomial relation makes the leading-coefficient multiple integral.

@stack 00PQ
-/

/- Lemma 10.123.1, tag 00PQ: a polynomial relation makes the
leading-coefficient multiple of the element integral. -/
@[stacks 00PQ]
#check @RingHom.isIntegralElem_leadingCoeff_mul
