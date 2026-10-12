/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# The object property of being fibred over a base

This module owns the neutral object property underlying `FiberedCategoryOver`. Equivalence closure
belongs to the higher-level `Fibered.Equivalence.ObjectProperty` module.
-/

@[expose] public section

universe uBase vBase uTotal vTotal

namespace CategoryTheory.BasedCategory

/-- The object property on `BasedCategory C` selecting fibred projections. -/
abbrev isFibered (C : Type uBase) [Category.{vBase} C] :
    ObjectProperty (BasedCategory.{vTotal, uTotal} C) :=
  fun X ↦ X.p.IsFibered

end CategoryTheory.BasedCategory
