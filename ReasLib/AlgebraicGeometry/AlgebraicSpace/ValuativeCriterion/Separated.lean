/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# Separated morphisms and the valuative criterion

Separated morphisms of algebraic spaces satisfy the uniqueness part of the
valuative criterion. For such morphisms, the existence part is equivalent to
the existence of a lift over every original valuative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.Uniqueness

/-- A separated morphism of algebraic spaces satisfies the uniqueness part of the valuative criterion. -/
instance of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] : Uniqueness f := by
  sorry

/-- Any two lifts in a valuative commutative square for a separated morphism are equal. -/
theorem liftStruct_eq_of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Separated f] (sq : ValuativeCommSq f)
    (l₁ l₂ : sq.commSq.LiftStruct) : l₁ = l₂ := by
  exact (subsingleton_liftStruct sq).elim l₁ l₂

end ValuativeCriterion.Uniqueness

namespace ValuativeCommSq.Extension

/-- A valuative square for a separated morphism of algebraic spaces has a lift
whenever a dominating extension of that square has a lift. -/
theorem hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Separated f]
    {sq : ValuativeCommSq f} (e : sq.Extension) : sq.commSq.HasLift :=
  sorry

/-- A separated morphism of algebraic spaces admits a dotted lift
`Spec(R) ⟶ X` of a valuative square whenever an arbitrary extension of that
square already has a lift. -/
theorem exists_liftHom {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Separated f]
    {sq : ValuativeCommSq f} (e : sq.Extension) :
    ∃ l : ofOver sq.specR ⟶ X, sq.verticalMap ≫ l = sq.i₁ ∧ l ≫ f = sq.i₂ :=
  sorry

end ValuativeCommSq.Extension

namespace ValuativeCriterion.Existence

/-- For a separated morphism of algebraic spaces, the existence criterion
allowing dominating extensions is equivalent to the existence of lifts over
every original valuative square. -/
theorem iff_hasLift_of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Separated f] : Existence f ↔ ∀ sq : ValuativeCommSq f, sq.commSq.HasLift :=
  sorry

/-- If a separated morphism of algebraic spaces satisfies the existence part of
the valuative criterion, then every valuative square admits a dotted arrow. -/
theorem hasLift_of_separated {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Separated f] [Existence f] (sq : ValuativeCommSq f) : sq.commSq.HasLift :=
  iff_hasLift_of_separated.mp inferInstance sq

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace
