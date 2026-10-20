/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty
public import ReasLib.CategoryTheory.Fibered.CategoryOver.ObjectProperty
public import ReasLib.CategoryTheory.Fibered.Equivalence.Fiberedness

/-!
# The equivalence-closed property of being fibred over a base

This module records closure of the neutral `BasedCategory.isFibered` object property under
bicategorical equivalences.
-/

@[expose] public section

universe uBase vBase uTotal vTotal

namespace CategoryTheory.BasedCategory

/-- Fibredness is closed under the canonical bicategorical equivalences of `BasedCategory C`. -/
instance isFibered.isClosedUnderEquivalences
    (C : Type uBase) [Category.{vBase} C] :
    (isFibered C :
      ObjectProperty (BasedCategory.{vTotal, uTotal} C)).IsClosedUnderEquivalences := sorry
/- Proof strategy: transport the property with `BasedCategory.Equivalence.isFibered_iff`. -/

end CategoryTheory.BasedCategory
