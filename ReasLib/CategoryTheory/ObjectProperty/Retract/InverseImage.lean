/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Retract-Stable Inverse Images

Retract stability of an object property is preserved by inverse image along an arbitrary
functor, since functors preserve retract diagrams.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.IsStableUnderRetracts

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- The inverse image of a retract-stable object property is retract-stable. -/
@[stacks 05RT "retract stability under inverse image"]
instance inverseImage (P : ObjectProperty D) [P.IsStableUnderRetracts]
    (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts := sorry


end CategoryTheory.ObjectProperty.IsStableUnderRetracts
