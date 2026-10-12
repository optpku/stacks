/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Injective
import StacksCheckRecall
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Lemma 59.19.1 (Tag 03OV): the forgetful functor from abelian sheaves to
abelian presheaves preserves injective objects. -/
@[stacks 03OV] #check
  (CategoryTheory.Sheaf.sheafToPresheaf_preservesInjectiveObjects (C := C) (J := J) :
    (sheafToPresheaf J AddCommGrpCat.{max u v}).PreservesInjectiveObjects)
