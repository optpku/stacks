/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Coproduct Closure of Extension Constructions

This leaf records the binary-coproduct closure properties of extension and
retract constructions on object properties.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The extension product of binary-coproduct-closed object properties is binary-coproduct-closed. -/
@[stacks 0FX3]
instance extensionProduct_isClosedUnderBinaryCoproducts (P Q : ObjectProperty C)
    [P.IsClosedUnderBinaryCoproducts] [Q.IsClosedUnderBinaryCoproducts] :
    (extensionProduct P Q).IsClosedUnderBinaryCoproducts := sorry

/-- The retract closure of a binary-coproduct-closed object property is binary-coproduct-closed. -/
@[stacks 0FX3]
instance retractClosure_isClosedUnderBinaryCoproducts (P : ObjectProperty C)
    [P.IsClosedUnderBinaryCoproducts] :
    P.retractClosure.IsClosedUnderBinaryCoproducts := sorry

/-- Every iterated extension product of a binary-coproduct-closed object property is
binary-coproduct-closed. -/
@[stacks 0FX3]
instance extensionProductIter_isClosedUnderBinaryCoproducts (P : ObjectProperty C)
    [P.IsClosedUnderBinaryCoproducts] (n : ℕ) :
    (P.extensionProductIter n).IsClosedUnderBinaryCoproducts := sorry

end

end CategoryTheory.ObjectProperty
