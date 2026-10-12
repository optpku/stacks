/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Coproduct Closure of Triangulated Subcategories

This module supplies the coproduct counterparts to mathlib's product-closure
instances for triangulated object properties.  They are stated for arbitrary
preadditive pretriangulated categories, independently of any source chapter.
-/

namespace CategoryTheory.ObjectProperty

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A triangulated object property closed under isomorphisms is closed under binary
coproducts. -/
@[stacks 05QM]
instance isClosedUnderBinaryCoproducts_of_isTriangulated
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderBinaryCoproducts := sorry

/-- A triangulated object property closed under isomorphisms is closed under finite
coproducts. -/
@[stacks 05QM]
instance isClosedUnderFiniteCoproducts_of_isTriangulated
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderFiniteCoproducts := sorry

end CategoryTheory.ObjectProperty
