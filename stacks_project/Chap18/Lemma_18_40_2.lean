/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Point
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.2 (04ET) (1): local unit dichotomy gives the zero-or-local alternative on every
point stalk. -/
@[stacks 04ET "(1)"]
#check @Sheaf.LocalUnitDichotomy.stalk_zero_or_local

/- Lemma 18.40.2 (04ET) (2): with enough points, the stalkwise alternative detects local unit
dichotomy. -/
@[stacks 04ET "(2)"]
#check @Sheaf.localUnitDichotomy_iff_stalk_zero_or_local
