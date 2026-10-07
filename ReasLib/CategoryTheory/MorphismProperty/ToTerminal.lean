module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Object properties induced by morphisms to a terminal object
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [HasTerminal C]

/-- The object property obtained from a morphism property by testing the canonical morphism to a
terminal object; this is the generic owner used in Remark 26.21.18. -/
@[stacks 0816 "absolute morphism property"]
def toTerminal (P : MorphismProperty C) : ObjectProperty C :=
  fun X ↦ P (terminal.from X)

/-- Membership in `P.toTerminal` is the property of the terminal morphism. -/
@[simp, stacks 0816 "absolute morphism property membership"]
lemma toTerminal_apply (P : MorphismProperty C) (X : C) :
    P.toTerminal X ↔ P (terminal.from X) := sorry

/-- Passing a conjunction of morphism properties to objects commutes with conjunction. -/
@[simp, stacks 0816 "absolute conjunction of morphism properties"]
theorem toTerminal_inf (P Q : MorphismProperty C) (X : C) :
    (P ⊓ Q).toTerminal X ↔ P.toTerminal X ∧ Q.toTerminal X := sorry

variable (P : MorphismProperty C)

/-- Over a `P`-object, a morphism has `P` exactly when its source is a `P`-object, under the
standard composition and cancellation hypotheses. -/
@[stacks 0816]
theorem mem_iff_toTerminal [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    {X Y : C} (f : X ⟶ Y) (hY : P.toTerminal Y) :
    P f ↔ P.toTerminal X := sorry

variable [HasPullbacks C]

/-- Absolute `P`-objects are closed under pullback when `P` has the standard stability and
cancellation properties. -/
@[stacks 0816]
theorem toTerminal_pullback [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
    [P.IsStableUnderBaseChange] {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : P.toTerminal X) (hY : P.toTerminal Y) (hZ : P.toTerminal Z) :
    P.toTerminal (pullback f g) := sorry

end CategoryTheory.MorphismProperty
