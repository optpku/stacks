/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Category
import ReasLib.CategoryTheory.ConnectedComponents.Groupoid
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopy categories of locally groupoidal bicategories

For a `(2,1)`-category, equality in each homwise connected-component quotient is exactly
existence of a `2`-isomorphism.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory.HomotopyCategory.mkHom

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.IsLocallyGroupoid B]

/-- In a locally groupoidal bicategory, two represented homotopy-category morphisms are equal
exactly when the representing `1`-morphisms are `2`-isomorphic. -/
@[stacks 04SC "kernel of the locally groupoidal homotopy quotient"]
theorem eq_iff_isomorphic {X Y : B} {f g : X ⟶ Y} :
    Bicategory.HomotopyCategory.mkHom f =
        Bicategory.HomotopyCategory.mkHom g ↔
      IsIsomorphic f g := sorry

end CategoryTheory.Bicategory.HomotopyCategory.mkHom
