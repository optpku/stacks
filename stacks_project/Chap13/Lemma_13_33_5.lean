/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Limit.CountableCoproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u uI

/-!
# Lemma 13.33.5

Exact countable coproducts in an abelian category and the resulting coproducts
in its derived category are neutral derived-category infrastructure. The
shared owner is stated first for an arbitrary exact discrete coproduct shape;
the countable `AB4` hypothesis supplies that shape automatically.
-/

/- Lemma 13.33.5 (Stacks 0A5L) (1): if `A` has exact countable coproducts,
then `DerivedCategory A` has countable coproducts. -/
@[stacks 0A5L] #check
  @CategoryTheory.DerivedCategory.Coproduct.hasCountableCoproducts_of_countableAB4

/- Lemma 13.33.5 (Stacks 0A5L) (2): for a countable family of complexes,
the image of its termwise coproduct, with the canonical coprojections, is a
coproduct in the derived category. -/
@[stacks 0A5L] #check fun
  {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasCountableCoproducts A] [CountableAB4 A]
  {α : Type uI} [Countable α] (K : α → CochainComplex A ℤ) ↦
    DerivedCategory.Coproduct.cofanIsColimit_of_termwise K
