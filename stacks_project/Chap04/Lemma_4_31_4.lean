/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Biterminal
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable (F : A ⥤ C) (G : B ⥤ C)

/- Lemma 4.31.4: the explicit categorical pullback square, regarded in `Pith Cat`, is a
biterminal `2`-commutative square. -/
@[stacks 02X9]
#check (CategoryTheory.Limits.CategoricalPullback.catCommSqOver.toPith.isBiterminal F G :
  Bicategory.IsBiterminal
    (CategoricalPullback.catCommSqOver F G).toPith)
