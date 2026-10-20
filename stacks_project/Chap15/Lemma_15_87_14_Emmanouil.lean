/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.AddCommGrp
import StacksCheckRecall

/-!
# Lemma 15.87.14 (Emmanouil)

@stack 0CQA
-/

@[expose] public section

/-
Lemma 15.87.14 (Emmanouil) (Stacks 0CQA): a sequential inverse system of abelian groups is
Mittag-Leffler exactly when the canonical Milnor `R¹ lim` object vanishes both for the system and
for its stagewise countable coproduct.
-/

@[stacks 0CQA] #check
  @CategoryTheory.SequentialInverseSystem.IsMittagLeffler.iff_r1Vanishing_of_countableCoproduct

#check @CategoryTheory.SequentialInverseSystem.countableCoproduct
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1
