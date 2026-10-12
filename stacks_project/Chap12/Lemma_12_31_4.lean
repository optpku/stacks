/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Limits
import StacksCheckRecall

/-!
# Lemma 12.31.4

The four-term exact-sequence statement is owned by the neutral sequential inverse-limit API.
-/

/- Lemma 12.31.4: if `A ⟶ B ⟶ C ⟶ D` is an exact sequence of sequential
abelian-group systems and `A` is Mittag-Leffler, then
`lim B ⟶ lim C ⟶ lim D` is exact. -/
@[stacks 070B] #check
  CategoryTheory.ComposableArrows.Exact.limit_tail_of_isMittagLeffler
