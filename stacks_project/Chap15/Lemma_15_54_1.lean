/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Grp.Injective
import StacksCheckRecall

/-!
# Lemma 15.54.1

@stack 01D7
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.54.1 (01D7): an abelian group is injective in `AddCommGrpCat` if and only if it is
divisible, expressed by surjectivity of multiplication by every nonzero integer. -/
@[stacks 01D7 "injective abelian groups are exactly the divisible groups"]
#check fun (J : Type u) [AddCommGroup J] ↦
  (AddCommGrpCat.injective_iff_divisible J :
    Injective (AddCommGrpCat.of J) ↔
      ∀ n : ℤ, n ≠ 0 → Function.Surjective (n • · : J → J))
