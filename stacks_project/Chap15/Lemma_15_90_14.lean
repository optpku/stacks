module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Equivalence
import StacksCheckRecall

/-!
# Formal gluing on a principal-open cover

@stack 05EP
-/

@[expose] public section

/- Lemma 15.90.14 (1): under flatness and the unit-ideal hypothesis, `Can ⋙ H⁰` is naturally
isomorphic to the identity (inverse adjunction unit). -/
@[stacks 05EP "(1) degree-zero left quasi-inverse"]
#check @LocalizedModule.Away.FormalGluing.h0LeftQuasiInverseIso_of_flat_of_span_eq_top

/- Lemma 15.90.14 (2): under the same hypotheses, `H⁰ ⋙ Can` is naturally isomorphic to the
identity. -/
@[stacks 05EP "(2) formal-gluing right quasi-inverse"]
#check @LocalizedModule.Away.FormalGluing.h0RightQuasiInverseIso_of_flat_of_span_eq_top

/- Lemma 15.90.14 (3): canonical formal gluing is an equivalence on a flat principal-open
cover. -/
@[stacks 05EP "(3) formal gluing equivalence on a principal-open cover"]
#check @LocalizedModule.Away.FormalGluing.ofModuleFunctor_isEquivalence_of_flat_of_span_eq_top

/- The quasi-inverse equivalence itself, with `Can` and `H⁰` as functor and inverse. -/
@[stacks 05EP "(3) explicit quasi-inverse equivalence"]
#check @LocalizedModule.Away.FormalGluing.equivalence_of_flat_of_span_eq_top
