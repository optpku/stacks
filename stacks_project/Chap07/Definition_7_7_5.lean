/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCheckRecall
import ReasLib.CategoryTheory.Sites.SheafCategory

@[expose] public section

open CategoryTheory

universe w v u

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)

/- Definition 7.7.5: `Sh(C)` is the full subcategory of `PSh(C)` whose objects are the sheaves of
sets. -/
@[stacks 00VQ] #check
  (CategoryTheory.sheaf_eq_fullSubcategory J (Type w) :
    CategoryTheory.Sheaf J (Type w) =
      CategoryTheory.ObjectProperty.FullSubcategory
        (CategoryTheory.Presheaf.IsSheaf J (A := Type w)))
