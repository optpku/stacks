module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import stacks_project.Chap101.«101_39_1_1_ValuativeSquare»

/-!
# Uniqueness part of the valuative criterion for algebraic stacks

A morphism of algebraic stacks satisfies uniqueness when every valuative
2-commutative square has a thin dotted-arrow category with at most one
isomorphism class. This property is stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- A morphism of algebraic stacks satisfies the uniqueness part of the
valuative criterion when, for every valuative 2-commutative square, the
category of dotted arrows is either empty or a setoid with exactly one
isomorphism class. -/
@[mk_iff]
class Uniqueness {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Hom-spaces in the dotted-arrow category are subsingleton. -/
  isThin : ∀ sq : ValuativeCommSq f, Quiver.IsThin (DottedArrow sq.toCone)
  /-- Any two dotted arrows are isomorphic. -/
  uniqueIsoClass :
    ∀ (sq : ValuativeCommSq f) (A A' : DottedArrow sq.toCone), Nonempty (A ≅ A')

namespace Uniqueness

/-- Uniqueness means that every valuative square has a thin dotted-arrow
category with at most one isomorphism class. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Uniqueness f ↔
      (∀ sq : ValuativeCommSq f, Quiver.IsThin (DottedArrow sq.toCone)) ∧
        ∀ (sq : ValuativeCommSq f) (A A' : DottedArrow sq.toCone),
          Nonempty (A ≅ A') :=
  sorry

/-- The dotted-arrow category of a valuative square is thin. -/
theorem isThin_dottedArrow {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Uniqueness f]
    (sq : ValuativeCommSq f) : Quiver.IsThin (DottedArrow sq.toCone) :=
  sorry

/-- Any two dotted arrows of a valuative square are isomorphic. -/
theorem nonempty_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [Uniqueness f]
    (sq : ValuativeCommSq f) (A A' : DottedArrow sq.toCone) :
    Nonempty (A ≅ A') :=
  sorry

/-- The composition of morphisms of algebraic stacks satisfying uniqueness
again satisfies uniqueness. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Uniqueness f] [Uniqueness g] :
    Uniqueness (f ≫ g) :=
  sorry

end Uniqueness

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
