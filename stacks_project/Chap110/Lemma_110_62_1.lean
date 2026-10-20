/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Ext.Size
import StacksCheckRecall

/-!
# A big abelian category whose Ext-groups are proper classes
-/

@[expose] public section

universe u

/- Lemma 110.62.1: There exists a large abelian category whose Ext groups are
not small in the chosen universe. The phrase “proper class” is interpreted
relative to this universe level rather than as a claim that a Lean type lies
outside every universe.
-/
@[stacks 07JT] #check (CategoryTheory.Abelian.exists_not_hasExt :
  ∃ (C : Type (u + 1)) (_ : CategoryTheory.Category.{u} C)
    (_ : CategoryTheory.Abelian C),
    ¬ CategoryTheory.HasExt.{u} C)
