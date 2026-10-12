/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] (U : C) {I : Type w}

/- Definition 7.6.1: in a category C, a family of morphisms with fixed target is
an object U of C, an index type I (possibly empty), and morphisms Uᵢ ⟶ U for
each i ∈ I, written {Uᵢ ⟶ U}_{i ∈ I}. This is a FormalCoproduct in the slice
category Over U, with I the original index type and obj i the slice object of
Uᵢ ⟶ U. These fields retain the complete indexed arrow data, including empty
families and repeated arrows. The constructor ofArrows packages (I, Uᵢ, π). -/
@[stacks 0396] #check (CategoryTheory.Limits.FormalCoproduct.ofArrows :
  (objects : I → C) → (∀ index, objects index ⟶ U) →
    CategoryTheory.Limits.FormalCoproduct.{w} (CategoryTheory.Over U))

#check (CategoryTheory.Limits.FormalCoproduct.{w} (CategoryTheory.Over U) :
  Type (max (w + 1) u v))
