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
# Lattice Operations on Retract-Stable Object Properties

@stack 05RB

Object properties form a complete lattice pointwise. Retract stability is preserved by both
intersections and unions, including their arbitrarily indexed forms.
-/

universe w v u

namespace CategoryTheory.ObjectProperty.IsStableUnderRetracts

variable {C : Type u} [Category.{v} C]

/-- The intersection of two retract-stable object properties is retract-stable. -/
@[stacks 05RB "intersection of retract-stable object properties"]
instance inf (P Q : ObjectProperty C) [P.IsStableUnderRetracts] [Q.IsStableUnderRetracts] :
    (P ⊓ Q).IsStableUnderRetracts := sorry

/-- The union of two retract-stable object properties is retract-stable. -/
@[stacks 05RB "union of retract-stable object properties"]
instance sup (P Q : ObjectProperty C) [P.IsStableUnderRetracts] [Q.IsStableUnderRetracts] :
    (P ⊔ Q).IsStableUnderRetracts := sorry

/-- An arbitrary intersection of retract-stable object properties is retract-stable. -/
@[stacks 05RB "indexed intersections of retract-stable object properties"]
instance iInf {I : Type w} (P : I → ObjectProperty C)
    [∀ i, (P i).IsStableUnderRetracts] :
    (⨅ i, P i).IsStableUnderRetracts := sorry

/-- An arbitrary union of retract-stable object properties is retract-stable. -/
@[stacks 05RB "indexed unions of retract-stable object properties"]
instance iSup {I : Type w} (P : I → ObjectProperty C)
    [∀ i, (P i).IsStableUnderRetracts] :
    (⨆ i, P i).IsStableUnderRetracts := sorry

end CategoryTheory.ObjectProperty.IsStableUnderRetracts
