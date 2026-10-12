/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.Flat
import StacksCheckRecall

/-!
# Flat inverse limits over ideal-power quotients

@stack 0912
-/

@[expose] public section

/- Lemma 15.27.4 (1): tensoring a finite module with the inverse limit agrees with
the inverse limit of the stagewise tensors. -/
@[stacks 0912 "Lemma 15.27.4 (1)"]
#check @CategoryTheory.PNatInverseSystem.tensorLimitComparison_bijective

/- Lemma 15.27.4 (2): the inverse limit is flat. -/
@[stacks 0912 "Lemma 15.27.4 (2)"]
#check @CategoryTheory.PNatInverseSystem.limit_flat
