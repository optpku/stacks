/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.CountableLimit
import StacksCheckRecall

/-!
# Lemma 10.86.4

The countable inverse-limit theorem is owned by the neutral Mittag-Leffler limit API.

@stack 0598
-/

/- Lemma 10.86.4: a short exact row of inverse systems of abelian groups over a countable
directed preorder remains short exact on inverse limits when the left underlying `Type`-valued
system is Mittag-Leffler. -/
@[stacks 0598] #check
  CategoryTheory.ShortComplex.ShortExact.limit_of_countable_isMittagLeffler
