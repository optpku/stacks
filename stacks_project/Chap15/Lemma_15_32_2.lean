/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.QuasiRegular

/-!
# Lemma 15.32.2

@stack 07CW
-/

@[expose] public section

/-!
# Quasi-Regular Ideal Finite-Generation Recall

The common principal-open generation shape is owned by ReasLib, and
quasi-regularity supplies its direct finite-generation specialization.
-/

/- Lemma 15.32.2, tag 07CW: a quasi-regular ideal is finitely generated. -/
@[stacks 07CW "quasi-regular ideals are finitely generated"]
#check @Ideal.IsQuasiRegularIdeal.fg
