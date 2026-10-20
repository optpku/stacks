/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.Grp.Abelian
import StacksCheckRecall
import ReasLib.CategoryTheory.Sites.SheafCategory

@[expose] public section

open CategoryTheory

universe w v u

variable (C : Type u) [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Definition 59.11.4 (1): `Sh(C)` is the category of sheaves of sets on the site `(C, J)`. -/
@[stacks 03NO] #check
  (CategoryTheory.sheaf_eq_fullSubcategory J (Type w) :
    CategoryTheory.Sheaf J (Type w) =
      CategoryTheory.ObjectProperty.FullSubcategory
        (CategoryTheory.Presheaf.IsSheaf J (A := Type w)))

/- Definition 59.11.4 (2): `Ab(C)` is the category of abelian sheaves on the site `(C, J)`. -/
@[stacks 03NO] #check
  (CategoryTheory.sheaf_eq_fullSubcategory J (AddCommGrpCat.{w}) :
    CategoryTheory.Sheaf J AddCommGrpCat.{w} =
      CategoryTheory.ObjectProperty.FullSubcategory
        (CategoryTheory.Presheaf.IsSheaf J (A := AddCommGrpCat.{w})))
