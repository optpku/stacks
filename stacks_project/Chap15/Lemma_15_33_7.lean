/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski.FilteredColimit

/-!
# Lemma 15.33.7

@stack 07D5
-/

@[expose] public section

/- Lemma 15.33.7: the categorical predicate for filtered colimits of local
complete-intersection maps is owned by ReasLib. -/
#check @RingHom.IsFilteredColimitOfLocalCompleteIntersection

/- Lemma 15.33.7: the bundled left-edge injectivity and exactness result. -/
#check @presentation_jacobi_zariski_exact_sequence_with_zero_left_of_isFilteredColimitOfLocalCompleteIntersection

/- Lemma 15.33.7 (1), tag `07D5`: the left Jacobi-Zariski map is injective. -/
@[stacks 07D5 "(1)"]
#check @presentationJacobiZariskiLeftSequence_injective_f_of_filteredColimitOfLci

/- Lemma 15.33.7 (2), tag `07D5`: the left Jacobi-Zariski row is exact. -/
@[stacks 07D5 "(2)"]
#check @presentationJacobiZariskiLeftSequence_exact_of_filteredColimitOfLci
