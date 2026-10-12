/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.CountableLimit
import StacksCheckRecall

/-!
# Exactness of countable inverse limits of modules

@stack 03CA

The reusable API proves the result for every countable directed preorder; the
source case is its specialization to inverse sequences indexed by `ℕ`.
-/

@[expose] public section

/- Lemma 10.87.1 (Tag 03CA): a short exact inverse sequence of `R`-modules indexed by `ℕ` stays
short exact on inverse limits when its left system is Mittag-Leffler. -/
@[stacks 03CA]
#check @ModuleCat.ShortExact.limit_of_countable_isMittagLeffler
