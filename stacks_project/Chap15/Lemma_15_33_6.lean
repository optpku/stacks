/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski

/-!
# Lemma 15.33.6

@stack 07D4
-/

@[expose] public section

/- Lemma 15.33.6: the canonical presentation-level map and the left
Jacobi-Zariski short complex are owned by ReasLib. -/
#check @tensor_presentation_cotangent_h1_to_h1_cotangent
#check @presentationJacobiZariskiLeftSequence

/- Lemma 15.33.6 (1), tag `07D4`: the conormal row of the composite
presentation is short exact. -/
@[stacks 07D4 "(1)"]
#check @comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel

/- Lemma 15.33.6 (2), tag `07D4`: the left Jacobi-Zariski map is injective. -/
@[stacks 07D4 "(2)"]
#check @presentationJacobiZariskiLeftSequence_injective_f_of_koszul_regular_kernel

/- Lemma 15.33.6 (3), tag `07D4`: the left Jacobi-Zariski row is exact. -/
@[stacks 07D4 "(3)"]
#check @presentationJacobiZariskiLeftSequence_exact_of_koszul_regular_kernel
