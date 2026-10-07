module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity

/-!
# Lemma 15.30.15

@stack 066A
-/

@[expose] public section

/-! # Lemma 15.30.15: regularity depends only on a same-length generating family -/

/- Lemma 15.30.15 (1), tag `066A`: quasi-regularity is invariant under a
same-length change of generators with the same generated ideal. -/
@[stacks 066A "quasi-regularity is invariant under a same-length change of generators"]
#check @RingTheory.Sequence.IsQuasiRegularSequence.of_span_eq

/- Lemma 15.30.15 (2), tag `066A`: `H₁`-regularity is invariant under a
same-length change of generators with the same generated ideal. -/
@[stacks 066A "H1-regularity is invariant under a same-length change of generators"]
#check @RingTheory.Sequence.IsH1RegularSequence.of_span_eq

/- Lemma 15.30.15 (3), tag `066A`: Koszul-regularity is invariant under a
same-length change of generators with the same generated ideal. -/
@[stacks 066A "Koszul-regularity is invariant under a same-length change of generators"]
#check @RingTheory.Sequence.IsKoszulRegularSequence.of_span_eq
