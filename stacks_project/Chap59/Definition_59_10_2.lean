/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.IndexedSite
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory

variable {C : Type u} [CategoryTheory.Category.{v} C]

/- Definition 59.10.2: a site consists of a category together with chosen covering
families satisfying the isomorphism, locality, and base-change axioms. -/
@[stacks 03NH] #check
  (CategoryTheory.PreZeroHypercover.IsSite :
    (∀ target : C, Set (CategoryTheory.PreZeroHypercover.{v} target)) → Prop)
