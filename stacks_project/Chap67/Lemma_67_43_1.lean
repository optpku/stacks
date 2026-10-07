module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Separated morphisms satisfy uniqueness in the valuative criterion

A separated morphism of algebraic spaces has at most one dotted lift in every
solid valuative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.Uniqueness

/-- Lemma 67.43.1: If `f : X ⟶ Y` is a separated morphism of algebraic spaces over a
scheme `S`, then `f` satisfies the uniqueness part of the valuative criterion. -/
@[stacks 03KU]
instance of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] : Uniqueness f :=
  sorry

/-- Any two dotted lifts of a valuative commutative square for a separated morphism of
algebraic spaces are equal. -/
theorem liftStruct_eq_of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Separated f] (sq : ValuativeCommSq f)
    (l₁ l₂ : sq.commSq.LiftStruct) : l₁ = l₂ :=
  sorry

end ValuativeCriterion.Uniqueness

end AlgebraicGeometry.AlgebraicSpace
