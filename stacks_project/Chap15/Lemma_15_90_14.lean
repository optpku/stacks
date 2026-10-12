/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Equivalence
import StacksCheckRecall

/-!
# Formal gluing on a principal-open cover

@stack 05EP
-/

@[expose] public section

/- Lemma 15.90.14 (1): under flatness and the unit-ideal hypothesis, `Can ⋙ H⁰` is naturally
isomorphic to the identity. -/
@[stacks 05EP "(1) degree-zero left quasi-inverse"]
#check @LocalizedModule.Away.FormalGluing.h0LeftQuasiInverse_of_flat_of_span_eq_top

/- Lemma 15.90.14 (2): under the same hypotheses, `H⁰ ⋙ Can` is naturally isomorphic to the
identity. -/
@[stacks 05EP "(2) formal-gluing right quasi-inverse"]
#check @LocalizedModule.Away.FormalGluing.h0RightQuasiInverse_of_flat_of_span_eq_top

/- Lemma 15.90.14 (3): canonical formal gluing is an equivalence on a flat principal-open
cover. -/
@[stacks 05EP "(3) formal gluing equivalence on a principal-open cover"]
#check @LocalizedModule.Away.FormalGluing.ofModuleFunctor_isEquivalence_of_flat_of_span_eq_top
