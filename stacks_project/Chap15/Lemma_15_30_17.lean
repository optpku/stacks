/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity.UpperTriangular

/-!
# Universal upper-triangular regularization

@stack 068Q
-/

@[expose] public section

/- The explicit universal faithfully flat smooth base-change ring and transformed family. -/
#check @RingTheory.Sequence.UpperTriangular.Ring
#check @RingTheory.Sequence.UpperTriangular.family

/- Lemma 15.30.17 (1), tag `068Q`: the universal base-change ring is faithfully flat. -/
@[stacks 068Q "Lemma 15.30.17 (1)"]
#check @RingTheory.Sequence.UpperTriangular.faithfullyFlat

/- Lemma 15.30.17 (2), tag `068Q`: the universal base-change ring is smooth. -/
@[stacks 068Q "Lemma 15.30.17 (2)"]
#check @RingTheory.Sequence.UpperTriangular.smooth

/- Lemma 15.30.17 (3), tag `068Q`: the transformed proper Koszul-regular family is regular. -/
@[stacks 068Q "Lemma 15.30.17 (3)"]
#check @RingTheory.Sequence.IsKoszulRegularSequence.isRegular_upperTriangular

/- Lemma 15.30.17 (4), tag `068Q`: the original and transformed families generate the same
extended ideal. -/
@[stacks 068Q "Lemma 15.30.17 (4)"]
#check @RingTheory.Sequence.IsKoszulRegularSequence.map_span_eq_span_upperTriangular
