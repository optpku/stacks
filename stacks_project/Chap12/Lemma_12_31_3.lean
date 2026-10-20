/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Limits
import StacksCheckRecall

/-!
# Lemma 12.31.3

The three clauses are exposed by the neutral short-exact and Mittag-Leffler limit APIs.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

/- Lemma 12.31.3 (1): sequential inverse limits preserve exactness at the middle term. -/
@[stacks 02N1] #check
  (fun (S : ShortComplex (SequentialInverseSystem AddCommGrpCat)) (hS : S.ShortExact) ↦
    ShortComplex.ShortExact.limit_exact hS)

/- The same left-exact sequence has a monic left map. -/
@[stacks 02N1] #check
  (fun (S : ShortComplex (SequentialInverseSystem AddCommGrpCat)) (hS : S.ShortExact) ↦
    ShortComplex.ShortExact.limit_mono_f hS)

/- Lemma 12.31.3 (2): a quotient of a Mittag-Leffler system in a short exact row is
Mittag-Leffler. -/
@[stacks 02N1]
#check
  (fun (S : ShortComplex (SequentialInverseSystem AddCommGrpCat)) (hS : S.ShortExact)
      (hX₂ : S.X₂.IsMittagLeffler) ↦
    ShortComplex.ShortExact.MittagLeffler.right_of_middle hS hX₂)

/- Lemma 12.31.3 (3): a short exact row of sequential abelian-group systems remains short exact
on limits when its left term is Mittag-Leffler. -/
@[stacks 02N1]
#check
  (fun (S : ShortComplex (SequentialInverseSystem AddCommGrpCat)) (hS : S.ShortExact)
      (hX₁ : S.X₁.IsMittagLeffler) ↦
    ShortComplex.ShortExact.limit_of_isMittagLeffler hS hX₁)
